#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
File:       Report Downloading and Merging
Author:     Jeff Law
Created on: 22/06/2018 04:20 PM
Note:       Python 2.7

"""
from __future__ import division
import glob
import multiprocessing
import os
from Queue import Empty
import time
from datetime import timedelta, datetime
import googleads.adwords
import googleads.errors
import shutil
import logger
import warnings
import pandas as pd
import numpy as np
import string
import unicodedata
import requests
import ConfigParser
import csv
import re
from operator import itemgetter
import sys
from random import uniform

warnings.simplefilter(action='ignore', category=FutureWarning)
logger.logging.disable('WARNING')
charset = string.letters + string.digits + ' _-\'%%|,'
settings = ConfigParser.ConfigParser()
settings.read('setup.ini')
fullAuto = settings.getboolean('AUTOMATION', 'fullAuto')
if not fullAuto:
    days_offset = settings.getint('AUTOMATION', 'offset')
else:
    days_offset = 0
useOneOffs = settings.getboolean('AUTOMATION', 'useOneOffs')
oneOffs = []
if useOneOffs:
    oneOffs = settings.get('AUTOMATION', 'oneOffs')
    if ',' in oneOffs:
        oneOffs = [x.strip() for x in oneOffs.split(',')]
    else:
        oneOffs = [oneOffs]

issuedict = {2: 'DCL', 3: 'HOLD', 4: 'CHBK', 5: 'FSD', 6: 'CXL', 7: 'CXL (DCL)', 8: 'CXL (CHBK)', 9: 'NUB',
             10: 'CXL (NUB)', 14: 'CXL (OTHER)'}
st = re.compile('\d{2}')
# locale.setlocale(locale.LC_ALL, 'usa')
idre = re.compile('\[(.*?)\]')
outdir = '_OUTPUT\\'
indir = '_INPUT\\'
cname = {}
email = {}
issue = {}
bdate = {}
sdays = {}
sdate = {}
report_type = {}
d25_imps = {}
d15_imps = {}
city_imps = {}
clicks = {}
city_list = {}
bill_amount = {}
ttl_imps = {}
desk_imps = {}
mob_imps = {}
tab_imps = {}
age_imps = {}
exp_imps = {}
add_imps = {}
ch_imps = {}
cities = {}
ssset = set()
reids = set()
unk_imps = set()
unk_vals = set()
cityf = 0
demof = 0
konf = 0
invf = 0
invf2 = 0
date_format = '%m/%d/%Y'
d_f2 = '%B %Y'
d30 = True
now = (datetime.today() + timedelta(days=0 + days_offset)).strftime('%m-%d-%Y')
now2 = (datetime.today() + timedelta(days=0 + days_offset)).strftime('%b %Y')
bill_date = str(int((datetime.today() + timedelta(days=0 + days_offset)).strftime('%d')))
d25 = str(int((datetime.today() + timedelta(days=5 + days_offset)).strftime('%d')))
d10 = (datetime.today() - timedelta(days=10 - days_offset)).strftime('%d')
d15 = str(int((datetime.today() + timedelta(days=15 + days_offset)).strftime('%d')))
if int(bill_date) == 31:
    d30 = False
logf = outdir + 'log_' + now + '.txt'
sys.stdout = open(logf, 'wb')
sys.stderr = sys.stdout

# Timeout between retries in seconds.
BACKOFF_FACTOR = 5
# Maximum number of processes to spawn.
MAX_PROCESSES = multiprocessing.cpu_count()
# Maximum number of retries for 500 errors.
MAX_RETRIES = 5
# Maximum number of items to be sent in a single API response.
PAGE_SIZE = 100

# print os.getcwd()
# sys.exit()
INPUT_DIR = "HTML"
OUTPUT_DIR = indir
DOWNLOAD_DIR = os.path.join(OUTPUT_DIR, "Downloads")
REPORTS_DIR = os.path.join(DOWNLOAD_DIR, "Reports")
REPORTS_TEMP_DIR = os.path.join(DOWNLOAD_DIR, "Reports", "Temp")
settings = ConfigParser.ConfigParser()
settings.read('setup.ini')
days_offset = settings.getint('AUTOMATION', 'offset')

# adwords_client = googleads.adwords.AdWordsClient.LoadFromStorage(os.path.join(INPUT_DIR, "googleads.yaml"))
adwords_client = googleads.adwords.AdWordsClient.LoadFromStorage(os.path.join(INPUT_DIR, "googleads.yaml"))


def numbers(n):
    num = ''.join(char for char in n if char in string.digits)
    try:
        num = int(num)
    except:
        num = 0
    return num


def cleaner(s):
    return ''.join(char for char in str(s) if char in charset)


def percer(n, tote):
    if tote > 0:
        return int((n / tote) * 100)
    else:
        # #print '\n*** ERROR: Dividing by zero (Check Campaign / Total Views)!'
        # try:
        #     print ("WARNING: total views was zero for client:", code, cname[code])
        # except:
        #     print ("WARNING: total views was zero, couldn't get client name:", code)
        return 0


def cleanup(s):
    '''
    Cleans up the dirty naming Sales Agents give to Clients
    '''
    ss = s
    if '(' in s:
        s = re.sub(r'\([^)]*\)', '', s)
    s = s.replace('&', 'and')
    words = s.split()
    rlist = set()
    for word in words:
        if '@' in word or '.com' in word or re.search(st, word):
            rlist.add(word)
    for i in range(len(words)):
        if i > 0:
            if words[i].title() == words[i - 1].title():
                rlist.add(words[i])
    for w in rlist:
        try:
            words.remove(w)
        except:
            print 'Name Cleanup Error: %s not found in %s' % (w, s)
    sss = string.capwords(' '.join(words)).title().replace('And ', 'and ').replace('Realtor', '').replace('\"',
                                                                                                          '').strip().title()
    if ss != ' '.join(words):
        if ss not in ssset:
            # print '     \"%s\"  |-->|  \"%s\"' % (ss, sss)
            ssset.add(ss)
    return sss


def city_order(city_list_uns):
    city_list = sorted(city_list_uns, key=itemgetter(1), reverse=True)  # [:4]
    new_city_list = []
    for i in range(0, min(len(city_list), 4)):
        new_city_list.extend([city_list[i][0], city_list[i][1]])
    if len(new_city_list) < 8:
        n = 8 - len(new_city_list)
        for i in range(0, n):
            new_city_list.extend([''])
    return new_city_list


def city_order2(city_list_uns, value, code):
    city_list = sorted(city_list_uns, key=itemgetter(1), reverse=True)  # [:4]
    new_city_list = []
    value = int(value.replace('$', '').replace(',', '').split('.')[0])
    # print value, code
    # print 'VALUE = %s' % str(value)
    if value < 200:
        tier = 1
    elif value < 300:
        tier = 4
    elif value < 400:
        tier = 4
    elif value < 1900:
        tier = 8
    else:
        tier = 1
    endrange = int(min(len(city_list), tier))
    for i in range(0, endrange):
        imps = int(city_list[i][1])
        totes = sum(int(d[1]) for d in city_list[:endrange])
        perc = int(round((imps / totes) * 100, 0))
        new_city_list.extend([city_list[i][0].upper(), perc])
    if len(new_city_list) < 16:
        n = 16 - len(new_city_list)
        for i in range(0, n):
            if i % 2 == 0:
                new_city_list.extend(['-'])
            else:
                new_city_list.extend([0])
    # print code, ':', new_city_list
    return new_city_list


def create_directory_if_not_exist(path):
    """
    Creates directories if they do not exist already

    :param path:
    :return:
    """
    try:
        os.makedirs(path)
    except OSError as e:
        if not os.path.isdir(path):
            raise


def remove_disallowed_filename_chars(filename):
    """
    Removes the disallowed characters from a given filename in unicode. However, it doesn't make sure that the filename
    is a valid file name e.g. .txt will remain .txt

    :param filename:
    :return:
    """
    validFilenameChars = "-_.() %s%s" % (string.ascii_letters, string.digits)
    cleanedFilename = unicodedata.normalize('NFKD', filename).encode('ASCII', 'ignore')
    return ''.join(c for c in cleanedFilename if c in validFilenameChars)


def download_image(filepath, url):
    """
    Download the file on the url specified and saves it to the filepath

    :param filepath:
    :param url:
    :return:
    """
    img_data = requests.get(url).content

    with open(filepath, 'wb') as handler:
        handler.write(img_data)


def unique_file(file_path_without_extension, extension):
    """
    Given a file name with extension, checks if the file already exists, then provides another name for the file
    e.g. abc.txt exists would be renamed to
        abc (1).txt

    :param file_path_without_extension: file path without extension
    :param extension: extension of the file
    :return: unique file name with extension and counter
    """
    actual_name = "%s.%s" % (file_path_without_extension, extension)
    c = 1

    while os.path.exists(actual_name):
        actual_name = "%s (%d).%s" % (file_path_without_extension, c, extension)
        c = c + 1

    return actual_name


def delete_create_required_directories():
    """
    Create required directories, Deletes existing content in the output directory
    :return:
    """
    create_directory_if_not_exist(DOWNLOAD_DIR)
    shutil.rmtree(REPORTS_TEMP_DIR, ignore_errors=True)
    create_directory_if_not_exist(OUTPUT_DIR)
    create_directory_if_not_exist(REPORTS_TEMP_DIR)


def _DownloadReport(process_id, report_download_directory, customer_id,
                    report_definition):
    """Helper function used by ReportWorker to download customer report.

    Note that multiprocessing differs between Windows / Unix environments. A
    Process or its subclasses in Windows must be serializable with pickle, but
    that is not possible for AdWordsClient or ReportDownloader. This top-level
    function is used as a work-around for Windows support.

    Args:
      process_id: The PID of the process downloading the report.
      report_download_directory: A string indicating the directory where you
          would like to download the reports.
      customer_id: A str AdWords customer ID for which the report is being
          downloaded.
      report_definition: A dict containing the report definition to be used.

    Returns:
      A tuple indicating a boolean success/failure status, and dict request
      context.
    """
    report_downloader = (googleads.adwords.AdWordsClient.LoadFromStorage(os.path.join(INPUT_DIR, "googleads.yaml"))
                         .GetReportDownloader())

    filepath = os.path.join(report_download_directory,
                            '%s_%d.csv' % (report_definition['reportName'], customer_id))
    retry_count = 0

    while True:
        # print ('[%d/%d] Loading report for customer ID "%s" into "%s"...'
        # % (process_id, retry_count, customer_id, filepath))
        try:
            with open(filepath, 'wb') as handler:
                report_downloader.DownloadReport(
                    report_definition, output=handler,
                    client_customer_id=customer_id,
                    skip_report_header=True, skip_column_header=False,
                    # skip_report_summary=True, include_zero_impressions=True
                    skip_report_summary=True, include_zero_impressions=False
                )

            return True, {'customerId': customer_id, 'report': report_definition['reportName']}

        except googleads.errors.AdWordsReportError as e:
            if e.code == 500 and retry_count < MAX_RETRIES:
                time.sleep(retry_count * BACKOFF_FACTOR)
            else:
                # print ('Report failed for customer ID "%s" with code "%d" after "%d" '
                # 'retries.' % (customer_id, e.code, retry_count + 1))
                return False, {'customerId': customer_id, 'code': e.code, 'message': e.message,
                               'report': report_definition['reportName']}


class ReportWorker(multiprocessing.Process):
    """A worker Process used to download reports for a set of customer IDs."""

    def __init__(self, report_download_directory, report_definition,
                 input_queue, success_queue, failure_queue):
        """Initializes a ReportWorker.

        Args:
          report_download_directory: A string indicating the directory where you
            would like to download the reports.
          report_definition: A dict containing the report definition that you would
            like to run against all customer IDs in the input_queue.
          input_queue: A Queue instance containing all of the customer IDs that
            the report_definition will be run against.
          success_queue: A Queue instance that the details of successful report
            downloads will be saved to.
          failure_queue: A Queue instance that the details of failed report
            downloads will be saved to.
        """
        super(ReportWorker, self).__init__()
        self.report_download_directory = report_download_directory
        self.report_definition = report_definition
        self.input_queue = input_queue
        self.success_queue = success_queue
        self.failure_queue = failure_queue

    def run(self):
        while True:
            try:
                customer_id = self.input_queue.get(timeout=0.01)
            except Empty:
                break
            result = _DownloadReport(self.ident, self.report_download_directory,
                                     customer_id, self.report_definition)
            (self.success_queue if result[0] else self.failure_queue).put(result[1])


def get_customer_ids():
    """Retrieves all CustomerIds in the account hierarchy.

    Note that your configuration file must specify a client_customer_id belonging
    to an AdWords manager account.

    Args:
    Raises:
      Exception: if no CustomerIds could be found.
    Returns:
      A List instance containing all CustomerIds in the account hierarchy.
    """
    # For this example, we will use ManagedCustomerService to get all IDs in
    # hierarchy that do not belong to MCC accounts.
    managed_customer_service = adwords_client.GetService('ManagedCustomerService',
                                                         version='v201809')

    offset = 0

    # Get the account hierarchy for this account.
    selector = {
        'fields': ['CustomerId'],
        'predicates': [{
            'field': 'CanManageClients',
            'operator': 'EQUALS',
            'values': [False]
        }],
        'paging': {
            'startIndex': str(offset),
            'numberResults': str(PAGE_SIZE)
        }
    }

    id_list = []
    more_pages = True

    while more_pages:
        page = managed_customer_service.get(selector)

        if page and 'entries' in page and page['entries']:
            for entry in page['entries']:
                id_list.append(entry['customerId'])
        else:
            raise Exception('Can\'t retrieve any customer ID.')
        offset += PAGE_SIZE
        selector['paging']['startIndex'] = str(offset)
        more_pages = offset < int(page['totalNumEntries'])

    return id_list


def download_report_per_customer(customer_id_list, report_definition):
    """
    For each customer in the customer id list, downloads the reports in the REPORTS_DIR using the report definition
    :param customer_id_list:
    :param report_definition:{
        'reportName': '30_Days_Report',
        'dateRangeType': 'LAST_30_DAYS',
        'reportType': 'CAMPAIGN_PERFORMANCE_REPORT',
        'downloadFormat': 'CSV',
        'selector': {
            'fields': ['CampaignId', 'Impressions']
        }
    }
    :return:
    """
    reports_succeeded = multiprocessing.Queue()
    reports_failed = multiprocessing.Queue()

    input_queue = multiprocessing.Queue()
    for x in customer_id_list:
        input_queue.put(x)

    queue_size = len(customer_id_list)
    num_processes = min(queue_size, MAX_PROCESSES)
    # print 'Retrieving %d reports with %d processes:' % (num_processes, num_processes)

    # temp_dir = os.path.join(REPORTS_DIR, "tmp")
    # shutil.rmtree(temp_dir, ignore_errors=True)
    # create_directory_if_not_exist(temp_dir)

    # Start all the processes.
    processes = [ReportWorker(REPORTS_TEMP_DIR,
                              report_definition, input_queue, reports_succeeded,
                              reports_failed)
                 for _ in range(num_processes)]

    for process in processes:
        process.start()

    for process in processes:
        process.join()

    # print'Finished downloading reports with the following results:'
    while True:
        try:
            success = reports_succeeded.get(timeout=0.01)
        except Empty:
            break
        # print '\tReport for CustomerId "%d" succeeded.' % success['customerId']

    while True:
        try:
            failure = reports_failed.get(timeout=0.01)
        except Empty:
            break
        # print ('\tReport for CustomerId "%d" failed with error code "%s" and '
        # 'message: %s.' % (failure['customerId'], failure['code'],
        #                failure['message']))


def get_locations(location_id_list):
    """
    Returns a df which contains location id and location names
    :param location_id_list:
    :return:
    """

    if not location_id_list:
        return pd.DataFrame({'location_id': [], 'location_name': []})

    location_df = pd.read_csv(os.path.join(INPUT_DIR, "Cities_API_codes.csv"))
    location_df = location_df[location_df['Criteria ID'].isin(location_id_list)]
    location_df = location_df[['Criteria ID', 'Name']].copy()
    columns = ['location_id', 'location_name']
    location_df.columns = columns
    location_df[columns] = location_df[columns].convert_objects(convert_numeric=True)

    return location_df


def download_all_required_reports(customer_id_list):
    # days_offset = days relative to today for target date of reports -- e.g. yesterday = -1
    d31 = timedelta(days=(-32 + days_offset))
    d25 = timedelta(days=(-28 + days_offset))
    d15 = timedelta(days=(-15 + days_offset))
    today = timedelta(days=(0))

    # #################
    # 30 Days
    report_definition = {
        'reportName': '30_Days_Report',
        'dateRangeType': 'CUSTOM_DATE',
        'reportType': 'CAMPAIGN_PERFORMANCE_REPORT',
        'downloadFormat': 'CSV',
        'selector': {
            'fields': ['CampaignId', 'Impressions'],
            'dateRange': {
                'min': (datetime.today() + d31).strftime('%Y%m%d'),
                'max': (datetime.today() + today).strftime('%Y%m%d')
            }
        }
    }

    download_report_per_customer(customer_id_list, report_definition)

    #################
    # 25 Days
    report_definition = {
        'reportName': '25_Days_Report',
        'dateRangeType': 'CUSTOM_DATE',
        'reportType': 'CAMPAIGN_PERFORMANCE_REPORT',
        'downloadFormat': 'CSV',
        'selector': {
            'fields': ['CampaignId', 'Labels', 'LabelIds', 'Impressions'],
            'dateRange': {
                'min': (datetime.today() + d25).strftime('%Y%m%d'),
                'max': (datetime.today() + today).strftime('%Y%m%d')
            }
        }
    }

    download_report_per_customer(customer_id_list, report_definition)

    #################
    # 15 Days
    report_definition = {
        'reportName': '15_Days_Report',
        'dateRangeType': 'CUSTOM_DATE',
        'reportType': 'CAMPAIGN_PERFORMANCE_REPORT',
        'downloadFormat': 'CSV',
        'selector': {
            'fields': ['CampaignId', 'Impressions'],
            'dateRange': {
                'min': (datetime.today() + d15).strftime('%Y%m%d'),
                'max': (datetime.today() + today).strftime('%Y%m%d')
            }
        }
    }

    download_report_per_customer(customer_id_list, report_definition)

    #################
    # Age Range
    report_definition = {
        'reportName': 'Age_Range_Report',
        'dateRangeType': 'ALL_TIME',
        'reportType': 'AGE_RANGE_PERFORMANCE_REPORT',
        'downloadFormat': 'CSV',
        'selector': {
            'fields': ['CampaignId', 'Criteria', 'Impressions']
        }
    }

    download_report_per_customer(customer_id_list, report_definition)

    #################
    # Device
    report_definition = {
        'reportName': 'Device_Report',
        'dateRangeType': 'ALL_TIME',
        'reportType': 'CAMPAIGN_PERFORMANCE_REPORT',
        'downloadFormat': 'CSV',
        'selector': {
            'fields': ['CampaignId', 'Device', 'Impressions']
        }
    }

    download_report_per_customer(customer_id_list, report_definition)

    #################
    # City
    report_definition = {
        'reportName': 'Geo_Report',
        'dateRangeType': 'LAST_30_DAYS',
        'reportType': 'GEO_PERFORMANCE_REPORT',
        'downloadFormat': 'CSV',
        'selector': {
            'fields': ['CampaignId', 'CountryCriteriaId', 'CityCriteriaId', 'Impressions']
        }
    }

    download_report_per_customer(customer_id_list, report_definition)


def read_consolidated_report(report_name):
    ### Consolidate downloaded files in temp directory to the reports directory
    all_files = glob.glob(os.path.join(REPORTS_TEMP_DIR, report_name + "*.csv"))

    df_from_each_file = (pd.read_csv(f) for f in all_files)
    concatenated_df = pd.concat(df_from_each_file, ignore_index=True)

    # Convert the object datatypes to numeric, so that they can be merged, pandas 0.23 bug
    concatenated_df[concatenated_df.columns] = concatenated_df[concatenated_df.columns].convert_objects(
        convert_numeric=True)

    return concatenated_df


def get_all_campaigns(customer_id_list):
    """
    Returns all campaigns in the for the customer ids provided in the list
    :return: [{id: 1, name:'abc'}, {id:2, name:'cde'}]
    """

    # The function can be reused from the download_campaigns script as well
    def get_campaigns_for_current_account():
        """
        Returns all campaigns in the current ad account selected
        :return: [{id: 1, name:'abc'}, {id:2, name:'cde'}]
        """
        # Initialize appropriate service.
        campaign_service = adwords_client.GetService('CampaignService', version='v201809')

        # Construct selector and get all campaigns.
        offset = 0
        selector = {
            'fields': ['Id', 'Name', 'Status'],
            'paging': {
                'startIndex': str(offset),
                'numberResults': str(PAGE_SIZE)
            }
        }

        more_pages = True
        campaigns = []

        while more_pages:
            page = campaign_service.get(selector)

            # Display results.
            if 'entries' in page:
                for campaign in page['entries']:
                    campaigns.append({'campaign_id': campaign['id'], 'campaign_name': campaign['name']})
                    # # print ('Campaign with id "%s", name "%s", and status "%s" was '
                    #        'found.' % (campaign['id'], campaign['name'],
                    #                    campaign['status']))
            else:
                pass
                # print 'No campaigns were found.'

            offset += PAGE_SIZE
            selector['paging']['startIndex'] = str(offset)
            more_pages = offset < int(page['totalNumEntries'])

        return campaigns

    campaigns_list = []

    # For each ad account get the list of campaigns
    for customer_id in customer_id_list:
        adwords_client.SetClientCustomerId(customer_id)
        campaigns_list += get_campaigns_for_current_account()  # Append the list to the global list

    campaigns_df = pd.DataFrame(campaigns_list)
    # # print(campaigns_df)
    return campaigns_df


def main():
    # Determine list of customer IDs to retrieve report for.
    customer_id_list = get_customer_ids()
    # print("Customer ID list: ")
    # print(customer_id_list)

    # Get all campaigns
    campaigns_df = get_all_campaigns(customer_id_list)
    # print(campaigns_df)

    # Download all required reports
    delete_create_required_directories()
    download_all_required_reports(customer_id_list)

    # ======================
    #################
    # 30 Days
    days_30_report_df = read_consolidated_report("30_Days_Report")
    # print(days_30_report_df)

    #################
    # 25 Days
    days_25_report_df = read_consolidated_report("25_Days_Report")
    # print(days_25_report_df)

    #################
    # 15 Days
    days_15_report_df = read_consolidated_report("15_Days_Report")
    # print(days_15_report_df)

    #################
    # Age Range
    age_range_report_df = read_consolidated_report("Age_Range_Report")
    age_range_report_df = age_range_report_df.pivot_table(index="Campaign ID", columns="Age Range",
                                                          values="Impressions", aggfunc=np.sum)
    # print(age_range_report_df)

    #################
    # Device
    device_report_df = read_consolidated_report("Device_Report")
    device_report_df = device_report_df.pivot_table(index="Campaign ID", columns="Device", values="Impressions",
                                                    aggfunc=np.sum)
    # print(device_report_df)

    #################
    # City
    city_report_df = read_consolidated_report("Geo_Report")
    # # print(city_report_df)

    # sort by "val" descending and extract first 8 rows from each group, also rank them by impressions for each campaign
    city_report_df = city_report_df.sort_values('Impressions', ascending=False).groupby('Campaign ID').head(8)
    city_report_df['rank'] = city_report_df.groupby('Campaign ID')['Impressions'].rank(method='dense', ascending=False)

    # Get the city ids as list to get city names from the location service
    city_id_list = city_report_df["City"].drop_duplicates().tolist()
    city_name_lkp_df = get_locations(city_id_list)
    # # print(city_name_lkp_df)

    city_report_df = city_report_df.merge(city_name_lkp_df, how="left", left_on="City", right_on="location_id")

    # Pivot the city data frame with cities as the columns
    # We need to pivot separately for city names since they are strings and need to be aggregated as the first value
    city_report_pv_impressions_df = city_report_df.pivot_table(index='Campaign ID', columns=['rank'],
                                                               values='Impressions', aggfunc=np.sum)
    city_report_pv_impressions_df.columns = ["City_Impressions_" + str(int(col)) for col in
                                             city_report_pv_impressions_df.columns]
    city_report_pv_name_df = city_report_df.pivot_table(index='Campaign ID', columns=['rank'], values='location_name',
                                                        aggfunc="first")
    city_report_pv_name_df.columns = ["City_" + str(int(col)) for col in city_report_pv_name_df.columns]

    city_report_pv_df = city_report_pv_impressions_df.merge(city_report_pv_name_df, how="inner", left_index=True,
                                                            right_index=True)

    # print(city_report_pv_df)

    # ======================
    merged_df = campaigns_df.merge(days_30_report_df, how="left", left_on="campaign_id", right_on="Campaign ID")
    merged_df = merged_df.drop("Campaign ID", axis=1)
    merged_df = merged_df.rename(index=str, columns={"Impressions": "30 days Impressions"})

    merged_df = merged_df.merge(days_25_report_df, how="left", left_on="campaign_id", right_on="Campaign ID")
    merged_df = merged_df.drop("Campaign ID", axis=1)
    merged_df = merged_df.rename(index=str, columns={"Impressions": "25 days Impressions"})

    merged_df = merged_df.merge(days_15_report_df, how="left", left_on="campaign_id", right_on="Campaign ID")
    merged_df = merged_df.drop("Campaign ID", axis=1)
    merged_df = merged_df.rename(index=str, columns={"Impressions": "15 days Impressions"})

    merged_df = merged_df.merge(age_range_report_df, how="left", left_on="campaign_id", right_index=True)
    merged_df = merged_df.merge(device_report_df, how="left", left_on="campaign_id", right_index=True)
    merged_df = merged_df.merge(city_report_pv_df, how="left", left_on="campaign_id", right_index=True)

    # print("==============================")
    # print(merged_df)

    now = datetime.now().strftime('%m-%d-%y')
    output_file = unique_file(os.path.join(OUTPUT_DIR, "AdWords_%s" % now), "csv")
    merged_df.to_csv(path_or_buf=output_file)
    return output_file


def remove_temps(dlist, first):
    for d in dlist:
        try:
            shutil.rmtree(d, ignore_errors=True)
        except Exception as e:
            print e
    if first:
        for f_ in os.listdir(indir):
            if 'adwords' in f_.lower():
                try:
                    os.remove(os.path.join(indir, f_))
                except Exception as e:
                    print e


def dictize_adwords(f_):
    data = {}
    with open(f_, 'rbU') as inf:
        read = csv.DictReader(inf)
        for record in read:
            camp = record['campaign_name']
            if '[' in camp and ']' in camp:
                record['code'] = camp.split('[')[1].split(']')[0]
                for col in record:
                    if col == '':
                        col = 0
                    if '.' in str(col):
                        try:
                            col = int(col.split('.')[0])
                        except:
                            pass
                    try:
                        col = int(col)
                    except:
                        pass
                # Using DictReader column headers to create a dictionary for the phone number
                data[camp] = {k: v for k, v in record.items()}
    for camp in data:
        for pos in data[camp]:
            col = data[camp][pos]
            if col == '':
                col = 0
            if '.' in str(col):
                col = str(col).split('.')[0]
            try:
                col = int(col)
            except:
                pass
            data[camp][pos] = col
        data[camp]['code'] = str(data[camp]['code'])
    return data


def dictize_omega(f_):
    data = {}

    # Konfigure's output files are MESSY - gotta ascii-ize and skip a row...
    nonascii = bytearray(range(0x80, 0x100))
    kfixed = os.path.join(indir, 'konfixer.csv')

    with open(f_, 'rb') as infile, open(kfixed, 'wb') as outfile:
        infile.next()  # Skip false first row
        for line in infile:  # b'\n'-separated lines (Linux, OSX, Windows)
            outfile.write(line.replace('\x00', '').translate(None, nonascii))

    with open(kfixed, 'rbU') as inf:
        read = csv.DictReader(inf)
        for record in read:
            data[record['[Id]']] = {k: v for k, v in record.items()}

    return data


def process_dicts(adict, odict):
    # Omega first...
    for code in odict:
        today = timedelta(days=(days_offset))
        bd = odict[code]['Monthly Bill Day']
        try:
            bdate[code] = str(int(bd))
        except:
            bdate[code] = '0'
        try:
            prob = int(odict[code]['Customer Issue Status'])
        except:
            prob = 0
        issue[code] = prob
        if prob > 3:
            # If Client Canceled and Last Report Date has passed, SKIP
            try:
                lsd = odict[code]['Last Spoken to Client - (Date)'].split(' ')[0]
                lsd = datetime.strptime(lsd, '%m/%d/%Y')
                dd = (datetime.today() + today)
                delta = dd - lsd
                delta = delta.days
                if delta > 0:
                    # print code
                    continue
            except Exception as e:
                # print 'ERROR in Last Spoken to Date:', code, e
                continue
        fn = odict[code]['First Name']
        ln = odict[code]['Last Name']
        try:
            cname[code] = cleanup(' '.join([fn.strip(), ln.strip()])).replace('.', '').replace('\'', '').strip()
            email[code] = odict[code]['Email'].lower()
        except Exception as e:
            print code, e
            continue
        try:
            sd = odict[code]['Customer Start Date - (Date)'].split(' ')[0]
            sd = datetime.strptime(sd, '%m/%d/%Y')
            dd2 = (datetime.today() + today)  # today's date + offset
            delta2 = dd2 - sd
            ssd = delta2.days  # days since start date, including offset
        except Exception as e:
            ssd = 100
            print 'ERROR in Start Date:', sd, '--', code, '--', cname[code], '--', e
            continue
        sdate[code] = sd.strftime('%m/%d/%y')  # Customer Start Date
        sdays[code] = ssd
        try:
            exp = int(odict[code]['Base Impression Total'])
        except:
            exp = 0
        if exp == 0:
            try:
                exp = int(odict[code]['Phrase Search Rate'])
            except:
                exp = 0
        if exp < 1000:
            exp = 2000
            # print 'ERROR: Unknown Impressions for %s\n  Guessing 2000' % cname[code]
        exp_imps[code] = exp
        try:
            # print row['Account Value']
            bill_amount[code] = '${:,.2f}'.format(float(odict[code]['Account Value']))
            # print bill_amount[code]
        except:
            bill_amount[code] = '$139.95'
        if bdate[code] == bill_date:
            if d30 is not False and ssd > 20:
                report_type[code] = '30-Day'
        elif sdays[code] == 10:
            report_type[code] = '10-Day'
        elif (bdate[code] == d25 and ssd > 20):
            report_type[code] = '25-Day'

    # Okay, next we do 30d, 25d, 15d, because they're easiest...s
    # ttl_imps, #d25_imps, #d15_imps
    for camp in adict:
        # code = camp.split('[')[1].split(']')[0].strip()
        code = adict[camp]['code']
        if code not in ttl_imps:
            ttl_imps[code] = 0
            d25_imps[code] = 0
            d15_imps[code] = 0
            desk_imps[code] = 0
            mob_imps[code] = 0
            tab_imps[code] = 0
            clicks[code] = 0
            if code not in issue:
                issue[code] = 0
    for camp in adict:
        code = adict[camp]['code']
        ttl_imps[code] += int(adict[camp]['30 days Impressions'])
        d25_imps[code] += int(adict[camp]['25 days Impressions'])
        d15_imps[code] += int(adict[camp]['15 days Impressions'])
        desk_imps[code] += int(adict[camp]['Computers'])
        mob_imps[code] += int(adict[camp]['Mobile devices with full browsers'])
        tab_imps[code] += int(adict[camp]['Tablets with full browsers'])

    ages = ['Undetermined', '18-24', '25-34', '35-44', '45-54', '55-64', '65 or more']
    for camp in adict:
        code = adict[camp]['code']
        city_imps[code] = []
        for i in range(1, 9):
            try:
                try:
                    city2 = odict[code]["City%s" % str(i)]
                except:
                    city2 = ''
                # if city2 == '':
                #     city2 = adict[camp]['City_%s' % str(i)]
                #     print 'Couldnt find City #%s in HubSpot for %s; using %s instead' % (str(i), camp, city2)
                city = adict[camp]['City_%s' % str(i)]
                impcs = adict[camp]['City_Impressions_%s' % str(i)]
                ccs = 0
                if city == 0 or city2 == '':
                    continue
                if ',' in city2:
                    city2 = city2.split(',')[0].strip()
                if 'unspecified' not in city.lower():
                    if code not in city_imps:
                        city_imps[code] = [(city2, impcs, ccs)]
                    elif city in [c[0] for c in city_imps[code]]:
                        index = [city_imps[code].index(c) for c in city_imps[code] if city == c[0]][0]
                        newtup = (city2, city_imps[code][index][1] + impcs, city_imps[code][index][2] + ccs)
                        city_imps[code][index] = newtup
                    else:
                        city_imps[code] += [(city2, impcs, ccs)]
                    # print code, city, impcs
            except Exception as e:
                print code, '--', e

        if city_imps[code] == [] and code in report_type and ttl_imps[code] > 0:
            # print "  No city impressions for campaign '%s'\n   Assigning %s 30-day impressions to City1: '%s'" % (adict[camp]["campaign_name"], str(ttl_imps[code]), odict[code]["City1"])
            city3 = (odict[code]["City1"])
            if ',' in city3:
                city3 = city3.split(',')[0].strip()
            city_imps[code] = [(city3, ttl_imps[code], 0)]

        for age in ages:
            try:
                if code not in age_imps:
                    age_imps[code] = [0] * len(ages)
                ind = ages.index(age)
                age_imps[code][ind] += adict[camp][age]
            except Exception as e:
                print code, '--', e


missed = set()
if __name__ == '__main__':

    pd.set_option('display.max_columns', 500)
    pd.set_option('display.width', 1000)
    remove_temps([DOWNLOAD_DIR, REPORTS_DIR, REPORTS_TEMP_DIR], first=True)

    print '\n--------------\nFORMATTER LOG:\n--------------\n'
    print 'REPORTS FOR DATE: %s' % now
    print 'Bill Date for 30-day Reports is: %s' % bill_date
    print 'Bill Date for 25-day Reports is: %s' % d25
    print 'Bill Date for 10-day Reports is: %s\n' % d10
    for f_ in os.listdir(indir):
        if 'omega' in f_.lower():
            omega_file = os.path.join(indir, f_)

    adwords_file = main()
    # adwords_file = os.path.join('_INPUT', 'AdWords_07-17-18.csv')
    adict = dictize_adwords(adwords_file)
    odict = dictize_omega(omega_file)
    process_dicts(adict, odict)
    delset = set()

    outfn = outdir + 'CS_DB.csv'
    outfn2 = outdir + 'LOAD_AI_' + now + '.xml'
    outfn3 = outdir + 'Reports_' + now + '.csv'
    outfn4 = outdir + 'MISSED_REPORTS_' + now + '.csv'

    with open(outfn, 'wb') as outf1:
        outwriter = csv.writer(outf1)
        outwriter.writerow(
            ['CName', 'ID', 'Email', 'Issue', 'Bdate', 'TTL Imps', 'Clicks', 'City1', 'City1 Imps', 'City2',
             'City2 Imps',
             'City3', 'City3 Imps', 'City4', 'City4 Imps', 'Unknown Age', '18-24', '25-34', '35-44', '45-54', '55-64',
             '65+',
             'Mobile', 'Desktop', 'Tablet', '25-day', '25/30 %', 'Value'])
        for code in city_imps:
            # try:
            if code in cname:
                list1 = [cname[code], code, email[code], issue[code], bdate[code], ttl_imps[code], clicks[code]]
            else:
                if code in reids:
                    print '  !!!ERROR: ID %s removed from CD_DB file' % code
                continue

            # if city_imps[code] == [] and code in report_type:
            #    print ("WARNING: no city impressions for campaign", cname[code])

            list2 = city_order(city_imps[code])[:8]
            list3 = age_imps[code]
            if sum([int(i) for i in list3]) == 0 and code in report_type:
                delset.add(code)
                # print '\n   !!!ERROR: %s has no Age Graph Data for %s Report!\n    ***SKIPPING REPORT***\n' % (cname[code], report_type[code])
                # if '30' in report_type[code]:
                #     print '   ***WARNING***: %s is a 30-Day Client!\n---------' % cname[code]
            list4 = [mob_imps[code], desk_imps[code], tab_imps[code], d25_imps[code],
                     int((d25_imps[code] / exp_imps[code]) * 100), bill_amount[code]]
            l2 = [list1, list2, list3, list4]
            outwriter.writerow([item for sublist in l2 for item in sublist])
            # except Exception as e:
            #     print '\n  !!!ERROR in Output for ID %s: %s\n' % (code, e)
            #     pass

    time.sleep(1)
    rowdict = {}
    with open(outfn, 'rbU') as inf:
        read = csv.reader(inf)
        read.next()
        for row in read:
            try:
                bd = int(row[4])
                if useOneOffs and not fullAuto and row[1] in oneOffs:
                    rowdict[row[1]] = row
                    report_type[row[1]] = 'Manual'
                elif row[1] in report_type:
                    if '25' in report_type[row[1]]:
                        rowdict[row[1]] = row
            except:
                pass
    with open(outfn3, 'wb') as outf, open(outfn4, 'wb') as outf4:
        outwriter = csv.writer(outf)
        outwriter4 = csv.writer(outf4)
        outwriter.writerow(
            ['Report_Type', 'CName', 'ID', 'Email', 'Issue', 'Bdate', 'Report Imps', 'Exp\'d Imps', 'Percent',
             'Age days', 'Start date', 'Acct Value'])
        outwriter4.writerow(
            ['Report_Type', 'CName', 'ID', 'Email', 'Issue', 'Bdate', 'Report Imps', 'Exp\'d Imps', 'Percent',
             'Age days', 'Start date', 'Acct Value'])
        for code in rowdict:
            if '30' in report_type[code]:
                # if ttl_imps[code] < exp_imps[code]:
                # cur_imps = ttl_imps[code]
                # rand = uniform(1.2,1.7)
                # ttl_imps[code] = int(exp_imps[code] * rand)
                # print '\n---------\n*** WARNING: %s Under Impressions Guarantee at 30 Days! (%s%%) | KID = [%s]\n  SKIPPING REPORT!\n--------------' % (cname[code], str(percer(ttl_imps[code], exp_imps[code])), code)
                delset.add(code)
                # print 'DEBUG: New value = %i\n' % ttl_imps[code]
                continue
            if '25' in report_type[code]:
                if ttl_imps[code] > (1.2 * exp_imps[code]):
                    rand = uniform(1.01, 1.2)
                    ttl_imps[code] = int(exp_imps[code] * rand)
                    d25_imps[code] = ttl_imps[code]
                if ttl_imps[code] < (exp_imps[code] * 0.74):
                    # cur_imps = ttl_imps[code]
                    # rand = uniform(1.2,1.7)
                    # ttl_imps[code] = int(exp_imps[code] * rand)
                    print '\n---------\n*** WARNING: %s Under Impressions Guarantee at 25 Days! (%s%%) | KID = [%s]\n  SKIPPING REPORT!\n--------------' % (
                        cname[code], str(percer(ttl_imps[code], exp_imps[code])), code)
                    missed.add(code)
                    delset.add(code)
                    # print 'DEBUG: New value = %i\n' % ttl_imps[code]
                    # continue
            # elif '30' in report_type[code]:
            #     if ttl_imps[code] > (2 * exp_imps[code]):
            #         rand = uniform(1.5, 1.7)
            #         ttl_imps[code] = int(exp_imps[code] * rand)
            l1 = [report_type[code]]
            l2 = rowdict[code][:5]
            l3 = [d25_imps[code] if '25' in report_type[code] else ttl_imps[code], exp_imps[code],
                  percer(d25_imps[code], exp_imps[code]) if '25' in report_type[code] else percer(ttl_imps[code],
                                                                                                  exp_imps[code]),
                  sdays[code], sdate[code], bill_amount[code]]
            l4 = [l1, l2, l3]
            if int(l3[0]) == 0:
                # print '\n*** WARNING: %s at 0 views for %s Report | KID = [%s]\n  SKIPPING REPORT!' % (l2[0], l1[0], l2[1])
                # d25_imps[code] = int(uniform(0.5,1.0) * exp_imps[code])
                delset.add(code)
                # continue
            # try:
            #     if int(l3[2]) < 50 and '25' in l1[0]:
            #         print '\n*** WARNING: %s under 50%% for %s Report | KID = [%s]\n  SKIPPING REPORT!' % (l2[0], l1[0], l2[1])
            #         d25_imps[code] = int(uniform(0.5,1.0) * exp_imps[code])
            #         delset.add(code)
            #         continue
            # except:
            #     print 'DEBUG: Percentage-check error'
            if code in missed:
                outwriter4.writerow([item for sublist in l4 for item in sublist])
                continue
            if code in delset:
                continue
            outwriter.writerow([item for sublist in l4 for item in sublist])

    print '\n---------\n DELETING ALL 30-DAY REPORTS! \n---------\n'
    # for code in report_type:
    #     if report_type[code] == '30-Day' and code in rowdict:
    #         delset.add(code)

    for code in delset:
        try:
            del rowdict[code]
        except Exception as e:
            print '\n ERROR DELETING CODE:', code, e, '\n'
    # for code in report_type:
    #     if report_type[code] == '30-Day':
    #         if code in exp_imps and code in ttl_imps and code in cname:
    #             if ttl_imps[code] < exp_imps[code]:
    #                 print '\n*** WARNING: %s Under Impressions Guarantee at 30 Days! (%s%%) | KID = [%s]' % (cname[code], str(percer(ttl_imps[code], exp_imps[code])), str(code))

    with open(outfn2, 'wb') as outf:
        outf.write('''<?xml version="1.0" encoding="utf-8"?>
    <!DOCTYPE svg PUBLIC "-//W3C//DTD SVG 20001102//EN"    "http://www.w3.org/TR/2000/CR-SVG-20001102/DTD/svg-20001102.dtd" [
    \t<!ENTITY ns_graphs "http://ns.adobe.com/Graphs/1.0/">
    \t<!ENTITY ns_vars "http://ns.adobe.com/Variables/1.0/">
    \t<!ENTITY ns_imrep "http://ns.adobe.com/ImageReplacement/1.0/">
    \t<!ENTITY ns_custom "http://ns.adobe.com/GenericCustomNamespace/1.0/">
    \t<!ENTITY ns_flows "http://ns.adobe.com/Flows/1.0/">
    <!ENTITY ns_extend "http://ns.adobe.com/Extensibility/1.0/">
    ]>
    <svg>
    <variableSets  xmlns="&ns_vars;">
    \t<variableSet  locked="none" varSetName="binding1">
    \t\t<variables>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City1"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City2"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City3"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City4"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City5"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City6"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City7"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City8"></variable>
    \t\t\t<variable  category="&ns_graphs;" trait="graphdata" varName="CityGraph"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="Total_Imps"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="Report_Type"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="NAME_MONTH_YEAR"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City1Perc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City2Perc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City3Perc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City4Perc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City5Perc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City6Perc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City7Perc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="City8Perc"></variable>
    \t\t\t<variable  category="&ns_graphs;" trait="graphdata" varName="AgesGraph"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="DesktopPerc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="TabletPerc"></variable>
    \t\t\t<variable  category="&ns_flows;" trait="textcontent" varName="MobilePerc"></variable>
    \t\t</variables>
    \t\t<v:sampleDataSets  xmlns="&ns_custom;" xmlns:v="&ns_vars;">''')
        for code in rowdict:
            aifn = code + '_' + cname[code].replace(' ', '_') + '_' + report_type[code] + '_' + now
            cp = city_order2(city_imps[code], bill_amount[code], code)
            cities = [cp[i].upper() for i in [0, 2, 4, 6, 8, 10, 12, 14]]
            percs = [cp[i] for i in [1, 3, 5, 7, 9, 11, 13, 15]]
            dtotes = sum([desk_imps[code], tab_imps[code], mob_imps[code]])
            l1 = [aifn]
            l2 = cities
            l3 = cp
            l4 = ['{:,}'.format(d25_imps[code]) if '25' in report_type[code] else '{:,}'.format(ttl_imps[code])]
            l5 = [report_type[code]]
            l6 = ['%s | %s' % (cname[code].upper(), now2.upper())]
            lp = ['%s%%' % percs[i] for i in range(0, len(percs)) if int(percs[i]) >= 6]
            l7 = lp + ([' '] * (len(percs) - len(lp)))  # percs[len(lp):len(percs)]
            l8 = [age_imps[code][i] for i in range(1, 7)]
            l9 = [percer(desk_imps[code], dtotes), percer(tab_imps[code], dtotes), percer(mob_imps[code], dtotes)]
            bigl = [l1, l2, l3, l4, l5, l6, l7, l8, l9]
            tl = [cleaner(item) for sublist in bigl for item in sublist]
            # print 'LENGTH: %s' % len(tl)
            outf.write('''\t\t\t<v:sampleDataSet  dataSetName="%s">
    \t\t\t\t<City1>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City1>
    \t\t\t\t<City2>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City2>
    \t\t\t\t<City3>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City3>
    \t\t\t\t<City4>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City4>
    \t\t\t\t<City5>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City5>
    \t\t\t\t<City6>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City6>
    \t\t\t\t<City7>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City7>
    \t\t\t\t<City8>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City8>
    \t\t\t\t<CityGraph>
    \t\t\t\t\t<data  numDataColumns="2">
    \t\t\t\t\t\t<values>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name">%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name">%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name">%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name">%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name">%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name">%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name">%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name">%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t</values>
    \t\t\t\t\t</data>
    \t\t\t\t</CityGraph>
    \t\t\t\t<Total_Imps>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</Total_Imps>
    \t\t\t\t<Report_Type>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</Report_Type>
    \t\t\t\t<NAME_MONTH_YEAR>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</NAME_MONTH_YEAR>
    \t\t\t\t<City1Perc>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City1Perc>
    \t\t\t\t<City2Perc>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City2Perc>
    \t\t\t\t<City3Perc>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City3Perc>
    \t\t\t\t<City4Perc>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City4Perc>
    \t\t\t\t<City5Perc>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City5Perc>
    \t\t\t\t<City6Perc>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City6Perc>
    \t\t\t\t<City7Perc>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City7Perc>
    \t\t\t\t<City8Perc>
    \t\t\t\t\t<p>%s</p>
    \t\t\t\t</City8Perc>
    \t\t\t\t<AgesGraph>
    \t\t\t\t\t<data  numDataColumns="7">
    \t\t\t\t\t\t<propertyRow  key="name">
    \t\t\t\t\t\t\t<value></value>
    \t\t\t\t\t\t\t<value>age 18 - 24</value>
    \t\t\t\t\t\t\t<value>age 25 - 34</value>
    \t\t\t\t\t\t\t<value>age 35 - 44</value>
    \t\t\t\t\t\t\t<value>age 45 - 54</value>
    \t\t\t\t\t\t\t<value>age 55 - 64</value>
    \t\t\t\t\t\t\t<value>age 65 +</value>
    \t\t\t\t\t\t</propertyRow>
    \t\t\t\t\t\t<values>
    \t\t\t\t\t\t\t<row>
    \t\t\t\t\t\t\t\t<value  key="name"></value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t\t<value>%s</value>
    \t\t\t\t\t\t\t</row>
    \t\t\t\t\t\t</values>
    \t\t\t\t\t</data>
    \t\t\t\t</AgesGraph>
    \t\t\t\t<DesktopPerc>
    \t\t\t\t\t<p>%s%%</p>
    \t\t\t\t</DesktopPerc>
    \t\t\t\t<TabletPerc>
    \t\t\t\t\t<p>%s%%</p>
    \t\t\t\t</TabletPerc>
    \t\t\t\t<MobilePerc>
    \t\t\t\t\t<p>%s%%</p>
    \t\t\t\t</MobilePerc>
    \t\t\t</v:sampleDataSet>
    ''' % tuple(tl))
        outf.write('''\t\t</v:sampleDataSets>
    \t</variableSet>
    </variableSets>
    </svg>
    ''')

    outf.close()

    remove_temps([DOWNLOAD_DIR, REPORTS_DIR, REPORTS_TEMP_DIR], first=False)
