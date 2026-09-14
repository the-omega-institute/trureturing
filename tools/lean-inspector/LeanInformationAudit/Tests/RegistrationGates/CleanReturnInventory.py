"""Pin positive exits and reject admission syntax without a reviewed rule ID.

This source contract is deliberately narrower than semantic classification.
Behavioral mutations separately exercise the statement and carrier fences.
"""
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / 'CleanReturnInventory.json'
SOURCE = HERE / '../../ReadoutProvenance.lean'


def scan(source):
    bodies, markers = {}, {}
    function = None
    pending = None
    for line in source.splitlines():
        match = re.match(r'(?:private |partial )*def ([A-Za-z_][A-Za-z0-9_.?]*)', line)
        if match:
            function = match[1]
            bodies[function] = []
        text = line.strip()
        mark = re.match(r'-- admission-exit: (\S+) rule=(\S*)$', text)
        if mark:
            pending = (mark[1], mark[2], function)
        elif text and not text.startswith('--'):
            if function:
                bodies[function].append(text)
            if pending:
                ident, rule, owner = pending
                if ident in markers:
                    markers[ident] = None
                else:
                    markers[ident] = (owner, rule, text)
                pending = None
    return bodies, markers


def check(source, manifest):
    bodies, markers = scan(source)
    enum = source.split('inductive ProvenanceAllowRule where', 1)
    rules = set(re.findall(r'\b\w+\b', enum[1].split('deriving', 1)[0])) if len(enum) == 2 else set()
    failures = []
    expected = {(row['function'], row['source']) for row in manifest['entries']}
    for row in manifest['entries']:
        rule = row['rule_id']
        guards = all(guard in bodies.get(row['function'], [])
                     for guard in row.get('requires', []))
        if not guards or markers.get(row['id']) != (row['function'], rule, row['source']) or not rule or (
                row['kind'] == 'production' and rule not in rules):
            failures.append('CleanReturnInventory.' + row['id'])
    registered_ids = {row['id'] for row in manifest['entries']}
    failures.extend('CleanReturnInventory.Unregistered.' + ident
                    for ident in markers if ident not in registered_ids)
    for name, lines in bodies.items():
        for line in lines:
            positive = re.search(r'(?:witness|checkedType) \.(\w+)', line)
            rejection = line.endswith('mentions true') or line.endswith('(mentions || rm) true')
            constructor = re.search(r'(?:return|pure).*\.(?:allowlisted|recognized|data)\b', line)
            constructor = constructor or re.search(r'=> \.(?:allowlisted|recognized|data)\b', line)
            tail = re.match(r'^(inputType|statementOuter|listStatementBoundary|dataCarrier|typeFamilyArgument|nominalFieldShape) env ', line)
            if ((positive and not rejection) or tail or constructor) and (name, line) not in expected:
                failures.append('CleanReturnInventory.Unregistered.' + name)
            if re.search(r'\b(?:return|pure)\s+(?:clean|defaultAdmit)\b', line):
                failures.append('CleanReturnInventory.MissingRuleId.' + name)
    for line in bodies.get('provenanceErrorCurrent', []):
        if 'return none' in line and not all(token in line for token in [
                'result.admission.isSome', '!result.forbidden',
                'result.unclassified.isNone', '!result.incomplete']):
            failures.append('CleanReturnInventory.PublicAdmission')
    return list(dict.fromkeys(failures))



def default_admit_mutation(source, entry):
    """A source-contract attack; deliberately rejected before elaboration."""
    lines = source.splitlines(True)
    marker = '-- admission-exit: ' + entry['id'] + ' rule='
    positions = [i + 1 for i, line in enumerate(lines) if marker in line]
    if len(positions) != 1 or lines[positions[0]].strip() != entry['source']:
        raise ValueError('Unresolved admission exit: ' + entry['id'])
    index = positions[0]
    indent = lines[index][:len(lines[index]) - len(lines[index].lstrip())]
    lines[index] = indent + 'return defaultAdmit\n'
    return ''.join(lines)


def main():
    manifest = json.loads(MANIFEST.read_text())
    source = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else SOURCE.read_text()
    failures = check(source, manifest)
    if failures:
        for name in failures:
            print('[FAIL] ' + name)
        return 1
    for row in manifest['entries']:
        print('[PASS] CleanReturnInventory.' + row['id'] + ': rule=' + row['rule_id'])
    probe = json.loads(json.dumps(manifest))
    probe['entries'][0]['rule_id'] = ''
    if check(source, probe) != ['CleanReturnInventory.' + manifest['entries'][0]['id']]:
        print('[FAIL] CleanReturnInventory.MissingRuleControl')
        return 1
    print('[PASS] CleanReturnInventory.MissingRuleControl')
    for row in manifest['entries']:
        predicted = ['CleanReturnInventory.' + row['id'],
                     'CleanReturnInventory.MissingRuleId.' + row['function']]
        observed = check(default_admit_mutation(source, row), manifest)
        if sorted(observed) != sorted(predicted):
            print('[FAIL] CleanReturnInventory.DefaultAdmitControl.' + row['id'])
            return 1
        print('[PASS] CleanReturnInventory.DefaultAdmitControl.' + row['id'])
    print('[PASS] CleanReturnInventory: ' + str(len(manifest['entries'])) + ' exits')
    return 0


if __name__ == '__main__':
    sys.exit(main())
