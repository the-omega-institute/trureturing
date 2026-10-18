"""Existing gh, make, codex and broker doors; no alternate mathematical judge."""
import importlib.util
import hashlib
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import time

from runtime import Stop, decode
from workers import Workers

SLUG = 'the-omega-institute/trureturing'
API = 'repos/' + SLUG
URL = 'https://github.com/' + SLUG


def readout_module():
    path = Path(__file__).resolve().parents[1] / 'research_readouts/readouts.py'
    spec = importlib.util.spec_from_file_location('research_readouts_contract', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_prereg(carrier, prereg):
    module = readout_module()
    try:
        module.preregistration(prereg, carrier)
    except module.ContractError as error:
        raise Stop('CARRIER_CONFLICT', str(error)) from error


def check_commitment(carriers, prereg, registered_at, candidate_sha256):
    module = readout_module()
    try:
        records = [(kind, value, carrier) for carrier in carriers
                   for kind, value in module.blocks(carrier)]
        canonical = module.decode(json.dumps(prereg, allow_nan=False))
        if len(records) != 1 or records[0][0] != 'prereg' or records[0][1] != canonical:
            raise Stop('CARRIER_CONFLICT', 'missing/duplicate/changed preregistration or terminal exists')
        if hashlib.sha256(carriers[0]['body'].encode()).hexdigest() != candidate_sha256:
            raise Stop('CARRIER_CONFLICT', 'candidate source/task/readout was edited')
        carrier = records[0][2]
        if carrier['created_at'] != registered_at:
            raise Stop('CARRIER_CONFLICT', 'registration identity changed')
        validate_prereg(carrier, prereg)
    except module.ContractError as error:
        raise Stop('CARRIER_CONFLICT', str(error)) from error


class Backend(Workers):
    def head(self, timeout=5):
        return self.call(['git', 'rev-parse', 'HEAD'], timeout).strip()

    def gh(self, route, timeout, payload=None, paginate=False):
        argv = ['gh', 'api', route]
        if paginate:
            argv += ['--paginate', '--slurp']
        if payload is not None:
            argv += ['--method', 'POST', '--input', '-']
        raw = self.call(argv, timeout, '' if payload is None else json.dumps(payload))
        value = decode(raw)
        if not paginate:
            if not isinstance(value, dict):
                raise Stop('CARRIER_MALFORMED')
            return value
        if not isinstance(value, list) or not all(isinstance(page, list) for page in value):
            raise Stop('PAGINATION_MALFORMED', 'complete array pages required')
        return [item for page in value for item in page]

    @staticmethod
    def number(issue):
        match = re.fullmatch(re.escape(URL) + r'/issues/([1-9][0-9]*)', issue or '')
        if match is None:
            raise Stop('CARRIER_IDENTITY', str(issue))
        return match[1]

    def find(self, intent, timeout):
        if intent['kind'] == 'candidate':
            # No search-index consistency assumption; include closed issues and every page.
            records = self.gh(API + '/issues?state=all&per_page=100&since=' + intent['since'],
                              timeout, paginate=True)
            records = [x for x in records if 'pull_request' not in x]
        else:
            number = self.number(intent['issue'])
            records = self.gh(API + f'/issues/{number}/comments?per_page=100', timeout, paginate=True)
        if not all(isinstance(x, dict) and isinstance(x.get('body'), (str, type(None))) for x in records):
            raise Stop('CARRIER_MALFORMED')
        found = [x for x in records if intent['marker'] in (x['body'] or '')]
        for carrier in found:
            self.reference(carrier, intent)
        return found

    def reference(self, carrier, intent):
        module = readout_module()
        try:
            module.check_carrier(carrier, datetime.max.replace(tzinfo=timezone.utc))
        except module.ContractError as error:
            raise Stop('CARRIER_MALFORMED', str(error)) from error
        if intent['kind'] == 'candidate':
            self.number(carrier['html_url'])
            if 'pull_request' in carrier:
                raise Stop('CARRIER_IDENTITY', 'candidate carrier is a pull request')
        elif not re.fullmatch(re.escape(intent['issue']) + r'#issuecomment-[1-9][0-9]*',
                              carrier['html_url']):
            raise Stop('CARRIER_IDENTITY', carrier['html_url'])

    def publish(self, intent, timeout):
        payload = {'body': intent['body']}
        if intent['kind'] == 'candidate':
            route = API + '/issues'
            payload['title'] = 'Autonomous research unit ' + intent['marker'].split(':')[1]
        else:
            route = API + '/issues/' + self.number(intent['issue']) + '/comments'
        carrier = self.gh(route, timeout, payload=payload)
        self.reference(carrier, intent)
        return carrier

    def validate_prereg(self, carrier, prereg, timeout):
        validate_prereg(carrier, prereg)

    def check_commitment(self, issue, prereg, registered_at, candidate_sha256, timeout):
        deadline = time.monotonic() + timeout
        number = self.number(issue)
        carrier = self.gh(API + '/issues/' + number, deadline - time.monotonic())
        if carrier.get('html_url') != issue:
            raise Stop('CARRIER_IDENTITY', 'issue response does not match the requested carrier')
        comments = self.gh(API + '/issues/' + number + '/comments?per_page=100',
                           deadline - time.monotonic(), paginate=True)
        check_commitment([carrier, *comments], prereg, registered_at, candidate_sha256)

    def verify(self, modules, head, timeout):
        deadline = time.monotonic() + timeout
        for module in modules:
            if not (self.root / (module.replace('.', '/') + '.lean')).is_file():
                raise Stop('MODULE_MISSING', module)
        targets = ' '.join(modules)
        # The canonical report owns compilation, axiom checks and custody (including fib_analysis).
        self.call(['make', 'lean-report-scoped', 'LEAN_TARGETS=' + targets],
                  deadline - time.monotonic())
        self.call(['make', 'gate', 'BASE=' + head], deadline - time.monotonic())

    def readouts(self, issue, as_of, timeout):
        return decode(self.call(['make', '-s', '--no-print-directory', '-C', 'tools',
            'research-readouts', 'ISSUES=' + self.number(issue), 'AS_OF=' + as_of], timeout))
