#!/usr/bin/env python3
"""Recompute issue-backed prediction scores and research five-mode readings."""
import argparse
from datetime import datetime, timezone
from decimal import Decimal
from fractions import Fraction
import json
import re
import subprocess
import sys

REPOSITORY = 'the-omega-institute/trureturing'
URL_ROOT = 'https://github.com/' + REPOSITORY
API_ROOT = 'repos/' + REPOSITORY
MODES = {(0, 0, 0): 'p0', (1, 0, 0): 'p2', (0, 1, 0): 'p5',
         (1, 1, 0): 'p25', (0, 0, 1): 'p3'}
BLOCK = re.compile(r'^```research-(prereg|terminal)-v1[ \t]*\n(.*?)\n```[ \t]*$', re.M | re.S)


class ContractError(ValueError):
    """A named input failure; no partial aggregate is published."""


def fail(code, detail):
    raise ContractError(code + ': ' + detail)


def fields(value, required, where):
    if not isinstance(value, dict) or set(value) != set(required):
        fail('FIELDS', where + ' requires exactly ' + ', '.join(required))
    return value


def string(value, where):
    if not isinstance(value, str) or not value.strip():
        fail('TEXT', where + ' must be nonempty text')
    return value


def timestamp(value):
    if not isinstance(value, str) or not re.fullmatch(r'\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ', value):
        fail('TIMESTAMP', repr(value) + ' must be UTC YYYY-MM-DDTHH:MM:SSZ')
    try:
        return datetime.strptime(value, '%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc)
    except ValueError:
        fail('TIMESTAMP', value)


def probability(value, code='INVALID_PROBABILITY'):
    if isinstance(value, bool) or not isinstance(value, (int, float, Decimal)):
        fail(code, repr(value) + ' must be a finite JSON number in [0,1]')
    try:
        result = Fraction(str(value))
    except (ValueError, OverflowError):
        fail(code, repr(value) + ' must be finite')
    if not 0 <= result <= 1:
        fail(code, repr(value) + ' is outside [0,1]')
    return result


def pairs(items):
    result = {}
    for key, value in items:
        if key in result:
            fail('DUPLICATE_KEY', key)
        result[key] = value
    return result


def decode(raw):
    def constant(value):
        fail('JSON_NUMBER', value)
    try:
        return json.loads(raw, parse_float=Decimal, parse_constant=constant, object_pairs_hook=pairs)
    except json.JSONDecodeError as error:
        fail('JSON', str(error))


def blocks(carrier):
    body = carrier['body']
    matches = list(BLOCK.finditer(body))
    # A malformed/unsupported tagged block is not a missing prediction.
    if len(re.findall(r'^```research-', body, re.M)) != len(matches):
        fail('BLOCK', 'malformed or unsupported research block at ' + carrier['html_url'])
    return [(match[1], decode(match[2])) for match in matches]


def api_path(url):
    match = re.fullmatch(re.escape(URL_ROOT) + r'/(issues|pull)/(\d+)(?:#issuecomment-(\d+))?', url)
    if not match:
        fail('EVIDENCE_URL', repr(url) + ' is not a repository issue/PR body or issue comment')
    return (API_ROOT + '/issues/comments/' + match[3] if match[3]
            else API_ROOT + '/issues/' + match[2])


def check_carrier(carrier, as_of):
    if not isinstance(carrier, dict):
        fail('CARRIER', 'expected a GitHub REST issue/comment')
    for field in ('html_url', 'body', 'created_at', 'updated_at'):
        if field not in carrier:
            fail('FIELDS', 'carrier lacks ' + field)
    api_path(string(carrier['html_url'], 'html_url'))
    if not isinstance(carrier['body'], str):
        fail('TEXT', 'carrier.body must be text')
    created, updated = timestamp(carrier['created_at']), timestamp(carrier['updated_at'])
    if not created <= updated <= as_of:
        fail('CARRIER_TIME', carrier['html_url'] + ' has incoherent or future metadata')


def event(value):
    fields(value, ('statement', 'quantifiers'), 'event')
    string(value['statement'], 'event.statement')
    string(value['quantifiers'], 'event.quantifiers')
    return value


def classify(x, y, z):
    if any(type(bit) is not int or bit not in (0, 1) for bit in (x, y, z)) or x * z or y * z:
        fail('ILLEGAL_MODE', repr((x, y, z)) + ' violates binary coordinates or xz=yz=0')
    return MODES[(x, y, z)]


def citation(ref, sources):
    fields(ref, ('url', 'excerpt'), 'evidence reference')
    url, excerpt = string(ref['url'], 'evidence.url'), string(ref['excerpt'], 'evidence.excerpt')
    api_path(url)
    if url not in sources:
        fail('DANGLING_EVIDENCE', url)
    if excerpt not in sources[url]['body']:
        fail('EVIDENCE_MISMATCH', url + ' does not contain the cited excerpt')
    return excerpt


def preregistration(value, carrier):
    fields(value, ('event', 'deadline', 'scoring_rule',
                   'surprise_threshold', 'predictions'), 'preregistration')
    event(value['event'])
    registered, deadline = timestamp(carrier['created_at']), timestamp(value['deadline'])
    if carrier['created_at'] != carrier['updated_at']:
        fail('EDITED_PREREGISTRATION', carrier['html_url'])
    if not registered < deadline:
        fail('DEADLINE', value['deadline'])
    rule = value['scoring_rule']
    fields(rule, ('name', 'version'), 'scoring_rule')
    if rule['name'] != 'binary-brier' or type(rule['version']) is not int or rule['version'] != 1:
        fail('SCORING_RULE', 'only binary-brier version 1 is supported')
    threshold = probability(value['surprise_threshold'], 'INVALID_THRESHOLD')
    if not isinstance(value['predictions'], list):
        fail('FIELDS', 'predictions must be a list; [] means no predictions were obtained')
    seats, predictions = set(), []
    for forecast in value['predictions']:
        fields(forecast, ('seat', 'model_family', 'event', 'probability'), 'prediction')
        seat = string(forecast['seat'], 'prediction.seat')
        family = string(forecast['model_family'], 'prediction.model_family')
        if seat in seats:
            fail('DUPLICATE_SEAT', seat)
        seats.add(seat)
        if event(forecast['event']) != value['event']:
            fail('EVENT_MISMATCH', 'prediction from ' + seat)
        predictions.append((seat, family, probability(forecast['probability'])))
    return registered, deadline, threshold, sorted(predictions)


def terminal_record(value, carrier, sources):
    if carrier['created_at'] != carrier['updated_at']:
        fail('EDITED_TERMINAL', carrier['html_url'])
    fields(value, ('event', 'execution_started_at', 'status', 'settled_at',
                   'evidence', 'shape_evidence'), 'terminal')
    event(value['event'])
    started, published = timestamp(value['execution_started_at']), timestamp(carrier['created_at'])
    if started > published:
        fail('EXECUTION_TIME', carrier['html_url'])
    if value['status'] not in ('proved', 'refuted', 'invalid', 'unresolved'):
        fail('TERMINAL_STATUS', repr(value['status']))
    citation(value['evidence'], sources)
    settled, shape = None, None
    if value['status'] in ('proved', 'refuted'):
        settled = timestamp(value['settled_at'])
        if not started <= settled <= published:
            fail('SETTLEMENT_TIME', carrier['html_url'])
        if value['shape_evidence'] is not None:
            excerpt = citation(value['shape_evidence'], sources)
            match = re.fullmatch(r'proof_shape: (content|bind-only)', excerpt)
            if not match:
                fail('SHAPE_EVIDENCE', 'cite exactly one existing proof_shape line')
            shape = int(match[1] == 'content')
    elif value['settled_at'] is not None or value['shape_evidence'] is not None:
        fail('UNSETTLED_EVIDENCE', 'an unresolved/invalid attempt cannot claim settled content')
    return started, settled, shape


def unit_reading(item, sources, as_of):
    fields(item, ('issue', 'comments'), 'issue snapshot')
    issue, comments = item['issue'], item['comments']
    if not isinstance(comments, list):
        fail('FIELDS', 'comments must contain all REST issue comment pages')
    check_carrier(issue, as_of)
    url = issue['html_url']
    if not re.fullmatch(re.escape(URL_ROOT) + r'/issues/[1-9]\d*', url) or 'pull_request' in issue:
        fail('ISSUE_IDENTITY', 'research unit must be a preregistration issue: ' + url)
    records = {}
    for carrier in [issue] + comments:
        check_carrier(carrier, as_of)
        if carrier is not issue and not re.fullmatch(re.escape(url) + r'#issuecomment-[1-9]\d*', carrier['html_url']):
            fail('COMMENT_IDENTITY', carrier['html_url'])
        for kind, value in blocks(carrier):
            if kind == 'prereg' and carrier is issue:
                fail('PREREG_CARRIER', 'use an unchanged issue comment, not issue-wide updated_at')
            if kind in records:
                fail('DUPLICATE_BLOCK', kind + ' in ' + url)
            records[kind] = (value, carrier)
    reading = {'issue': url, 'event': None, 'x': None, 'y': None, 'z': None, 'mode': None,
               'aggregate_probability': None, 'surprise': None, 'scores': [],
               'model_families': [], 'registered_at': None, 'score_status': 'missing-preregistration',
               'evidence_status': 'missing-preregistration'}
    if 'terminal' in records:
        terminal, terminal_carrier = records['terminal']
        started, settled, shape = terminal_record(terminal, terminal_carrier, sources)
    if 'prereg' not in records:
        return reading
    prereg, carrier = records['prereg']
    registered, deadline, threshold, forecasts = preregistration(prereg, carrier)
    reading['event'] = prereg['event']
    reading['registered_at'] = carrier['created_at']
    reading['evidence_status'] = 'missing-terminal'
    reading['model_families'] = sorted({family for _, family, _ in forecasts})
    reading['aggregate_probability'] = str(sum((p for _, _, p in forecasts), Fraction()) / len(forecasts)) if forecasts else None
    answer, x = None, 0
    reading['z'] = 1
    if 'terminal' in records:
        if terminal['event'] != prereg['event']:
            fail('EVENT_MISMATCH', 'terminal in ' + url)
        if registered > started:
            fail('POSTHOC_PREDICTION', url)
        if not started < deadline:
            fail('EXECUTION_TIME', url)
        reading['evidence_status'] = 'referenced'
        if settled is not None and settled <= deadline:
            answer = int(terminal['status'] == 'proved')
            reading['z'] = 0
            x = shape
            if shape is None:
                reading['evidence_status'] = 'missing-shape'
    if answer is None and as_of < deadline:
        fail('BEFORE_DEADLINE', url + ' has no settled answer yet')
    reading['x'] = x
    if not forecasts:
        reading['score_status'] = 'missing-predictions'
        return reading
    if answer is None:
        reading['y'] = 0  # Structural zero under z=1, never a scored negative answer.
        reading['score_status'] = 'unsettled'
    else:
        scores = [(seat, family, (p - answer) ** 2) for seat, family, p in forecasts]
        reading['scores'] = [{'seat': seat, 'model_family': family, 'brier': str(score)}
                             for seat, family, score in scores]
        surprise = sum((score for _, _, score in scores), Fraction()) / len(scores)
        reading['surprise'] = str(surprise)
        reading['y'] = int(surprise >= threshold)
        reading['score_status'] = 'scored'
    if x is not None:
        reading['mode'] = classify(x, reading['y'], reading['z'])
    return reading


def recompute(batch, as_of):
    """Read complete REST snapshots; arithmetic is exact, without a cache or writes."""
    fields(batch, ('issues', 'evidence'), 'batch')
    now = timestamp(as_of)
    if not isinstance(batch['issues'], list) or not isinstance(batch['evidence'], list):
        fail('FIELDS', 'issues and evidence must be arrays')
    sources = {}
    all_sources = list(batch['evidence'])
    for item in batch['issues']:
        fields(item, ('issue', 'comments'), 'issue snapshot')
        if not isinstance(item['comments'], list):
            fail('FIELDS', 'comments must be an array')
        all_sources += [item['issue']] + item['comments']
    for source in all_sources:
        check_carrier(source, now)
        url = source['html_url']
        if url in sources and sources[url] != source:
            fail('CONFLICTING_SOURCE', url)
        sources[url] = source
    readings, seen = [], set()
    for item in batch['issues']:
        url = item['issue']['html_url']
        if url in seen:
            fail('DUPLICATE_UNIT', url)
        seen.add(url)
        readings.append(unit_reading(item, sources, now))
    readings.sort(key=lambda reading: reading['issue'])
    counts = dict.fromkeys(MODES.values(), 0)
    for reading in readings:
        if reading['mode'] is not None:
            counts[reading['mode']] += 1
    total, complete = len(readings), sum(counts.values())
    scored = sum(reading['score_status'] == 'scored' for reading in readings)
    def ratio(numerator, denominator):
        return str(Fraction(numerator, denominator)) if denominator else None
    summary = {'unit_count': total, 'scored_units': scored, 'mode_denominator': complete,
               'five_counts': counts, 'score_coverage': ratio(scored, total),
               'mode_coverage': ratio(complete, total),
               'X': ratio(counts['p2'] + counts['p25'], complete),
               'Y': ratio(counts['p5'] + counts['p25'], complete),
               'Z': ratio(counts['p3'], complete),
               'missing_counts': {
                   'prediction_units': sum(reading['aggregate_probability'] is None for reading in readings),
                   'answer_units': sum(reading['z'] != 0 for reading in readings),
                   'shape_units': sum(reading['x'] is None for reading in readings),
                   'mode_units': total - complete}}
    return {'format': 'research-readouts-v1', 'as_of': as_of, 'units': readings, 'batch': summary}


def gh_json(path, paginate=False):
    command = ['gh', 'api', path]
    if paginate:
        command += ['--paginate', '--slurp']
    try:
        result = subprocess.run(command, check=True, capture_output=True, text=True)
    except (OSError, subprocess.CalledProcessError) as error:
        fail('FETCH', str(error))
    return decode(result.stdout)


def load_issues(numbers):
    batch = {'issues': [], 'evidence': []}
    sources, refs = set(), set()
    for number in numbers:
        if type(number) is not int or number < 1:
            fail('ISSUE_IDENTITY', repr(number))
        issue = gh_json(API_ROOT + '/issues/' + str(number))
        pages = gh_json(API_ROOT + '/issues/' + str(number) + '/comments', paginate=True)
        if not isinstance(pages, list) or any(not isinstance(page, list) for page in pages):
            fail('FETCH', 'expected complete paginated comment arrays')
        comments = [comment for page in pages for comment in page]
        batch['issues'].append({'issue': issue, 'comments': comments})
        for carrier in [issue] + comments:
            check_carrier(carrier, datetime.max.replace(tzinfo=timezone.utc))
            sources.add(carrier['html_url'])
            for kind, record in blocks(carrier):
                if kind == 'terminal' and isinstance(record, dict):
                    for field in ('evidence', 'shape_evidence'):
                        ref = record.get(field)
                        if isinstance(ref, dict) and isinstance(ref.get('url'), str):
                            refs.add(ref['url'])
    for url in sorted(refs - sources):
        fetched = gh_json(api_path(url))
        if not isinstance(fetched, dict) or fetched.get('html_url') != url:
            fail('EVIDENCE_IDENTITY', url)
        batch['evidence'].append(fetched)
    return batch


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--as-of', required=True, help='UTC snapshot cutoff; unresolved units require their deadline')
    parser.add_argument('--issue', type=int, action='append', help='fetch this preregistration issue (repeatable); otherwise read REST snapshots from stdin')
    args = parser.parse_args()
    try:
        batch = load_issues(args.issue) if args.issue else decode(sys.stdin.read())
        result = recompute(batch, args.as_of)
        print(json.dumps(result, sort_keys=True, ensure_ascii=False))
        return 0
    except (ContractError, OSError) as error:
        print('READOUT ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
