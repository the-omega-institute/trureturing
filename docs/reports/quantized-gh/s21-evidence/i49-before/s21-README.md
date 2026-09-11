# S21 composed predecessor evidence

This contract exposes the exact S20 predecessor composition with the completed S21 pure tail. The active source is `source-S20-merged` (bytes `[0,364059)`) followed by `tail-S21-I37` (bytes `[364059,394734)`). The resulting source is 394734 bytes; its prefix is SHA256 `47880f8a0b5b96b7fa2178c5a92284da6ec8b112b33c6e14236719f6963c3d00`, the tail is SHA256 `bbfebd2a77ed6f98956d1e609e6fde8737e9713c7e8e7032b4a2da21f3c0dece`, and the composed identity is recorded in `composition.json`.

`source-I37-original`, `report-I37-original`, `I32-original`, `I35-original`, and `I37-original` are complete immutable historical inputs. Their descriptors list ordered raw UTF-8 parts, exact original byte and LF spans, per-part hashes, and source Git origins. Concatenate parts in ordinal order before parsing; no separators, trimming, normalization, compression, or reserialization is applied. `tail-S21-I37` is the exact 30,675-byte completed tail from original source offset 316725. Every raw part is at most 750 LF lines and every new directory has at most 40 direct files.

The `current-units.json` partition contains all 282 inherited S20 whole units and all 22 S21 units. S21 coordinates are translated by the checked delta 47334 from their original I37 coordinates. The 68-byte chapter 32 heading at `[364059,364127)` is an explicit structural region because `generic-v1` drops heading-only candidates. `own-addresses.json` retains 32.1–32.24 meanings and reserved 32.19/32.20 addresses. `canonical-pairs.json` points to the complete inherited S20 closure and records the 78 tail pair identities from the I35/I37 maps; 149 historical/current imported pairs remain caller-preserved, and no ingest was run.

The original S20 public README is preserved byte-for-byte as `s20-readme-before-s21.md`. Its consumer is extended with a bounded prefix API in the S20 contract: `source-S20-merged` is selected with checked bounds `[0,364059)`, while ordinary whole-file resources retain whole-file semantics. S19’s explicit prefix contract remains inherited unchanged.

## Fixed reconstruction API

```python
from pathlib import Path
import hashlib, json

ROOT = Path('.')
BASE = ROOT / 'docs/reports/quantized-gh/s21-evidence'
def read_parts(name):
    d = json.loads((BASE / (name + '.json')).read_text(encoding='utf-8'))
    chunks=[]; cursor=0
    for part in d['parts']:
        b=(ROOT / part['path']).read_bytes()
        if len(b) != part['bytes'] or hashlib.sha256(b).hexdigest() != part['sha256']:
            raise ValueError('part identity mismatch')
        if part['byte_span'] != [cursor, cursor + len(b)] or part['lines'] > 800:
            raise ValueError('part bounds or capacity mismatch')
        chunks.append(b); cursor += len(b)
    out=b''.join(chunks)
    if len(out) != d['original']['bytes'] or hashlib.sha256(out).hexdigest() != d['original']['sha256']:
        raise ValueError('resource identity mismatch')
    out.decode('utf-8')
    return out

def prefix(data, span):
    a,b=span
    if type(a) is not int or type(b) is not int or not 0 <= a <= b <= len(data):
        raise ValueError('invalid checked span')
    return data[a:b]

def resource(name):
    if name in {'source-I37-original','report-I37-original','I32-original','I35-original','I37-original','tail-S21-I37'}:
        return read_parts(name)
    if name == 'source-S20-merged':
        return prefix((ROOT/'docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md').read_bytes(), [0,364059])
    if name == 'source-composed-I48':
        return (ROOT/'docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md').read_bytes()
    if name == 'report-I37':
        return resource('report-I37-original')
    raise KeyError(name)

assert resource('source-composed-I48') == resource('source-S20-merged') + resource('tail-S21-I37')
json.loads(resource('I37-original'))
```

The API supports complete review access to every named version and preserves original report anchor ownership through the original report resource. Historical source/map offsets are interpreted only within their named original version. The composition remains a representation and provenance result; a fresh independent source review, caller sealing, ordinary CI, and delivery are still pending.
