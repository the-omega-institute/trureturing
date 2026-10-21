# Third-party licences

Tengoku is licensed under the Apache License, Version 2.0 (see [LICENSE](LICENSE)), **except** for the
third-party material listed below, which stays under its upstream licence. Nothing here relicenses anyone's work.

## 1. Seeded packages (`Tengoku/`)

The tree was seeded by folding the source files of these packages into topic paths (`scripts/seed.py`).
Seeded files are copied as they are upstream, copyright headers included wherever the upstream file has one;
the aggregator modules (`Tengoku/Seed/Std.lean` and the like) are generated.

| Package | Upstream | Licence | Folded into |
|---|---|---|---|
| Mathlib | [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | Apache-2.0 | `Tengoku/` (topic paths) |
| Batteries | [leanprover-community/batteries](https://github.com/leanprover-community/batteries) | Apache-2.0 | `Tengoku/Seed/Std/` |
| Aesop | [leanprover-community/aesop](https://github.com/leanprover-community/aesop) | Apache-2.0 | `Tengoku/Seed/Tactic/Aesop/` |
| Qq | [leanprover-community/quote4](https://github.com/leanprover-community/quote4) | Apache-2.0 | `Tengoku/Seed/Meta/Qq/` |
| ProofWidgets | [leanprover-community/ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) | Apache-2.0 | `Tengoku/Seed/Widgets/`, `widget/` |
| Plausible | [leanprover-community/plausible](https://github.com/leanprover-community/plausible) | Apache-2.0 | `Tengoku/Seed/Testing/Random/` |
| LeanSearchClient | [leanprover-community/LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | Apache-2.0 | `Tengoku/Seed/Search/LeanSearchClient/` |
| import-graph | [leanprover-community/import-graph](https://github.com/leanprover-community/import-graph) | Apache-2.0 | `Tengoku/Seed/Meta/ImportGraph/` |
| lean4-cli | [leanprover/lean4-cli](https://github.com/leanprover/lean4-cli) | MIT | `Tengoku/Seed/Meta/Cli/` |

lean4-cli is MIT-licensed: `Copyright (c) 2021 mhuisi` ([licence](https://github.com/leanprover/lean4-cli/blob/main/LICENSE)). The MIT permission notice is reproduced in section 4.

## 2. Records from registered libraries (`data/`) and the modules generated from them

Each record in `data/tentative/`, `data/staging/` and `data/trusted/` names its origin in `source_url`, and each
library's licence is recorded in `schemas/sources.json` (`licences`). A record, and any module under
`Tengoku/<Library>/` generated from it, is distributed under the licence of the library it came from.

The records in `data/trusted/mathlib-*.jsonl` describe the seeded Mathlib and are Apache-2.0 like it.

The records from [competemath.com](https://competemath.com/practice/problems) are Apache-2.0: their author
released them under it, and the site's terms release problems and proofs under it when posted.

94 registered libraries are Apache-2.0, the same licence as this repository; their copyright
notices are those of the upstream repositories linked in `schemas/sources.json`.

The libraries under other licences:

| Licence | Library | Registry keys | Upstream copyright | Files |
|---|---|---|---|---|
| BSD-3-Clause | [keilambda/ttfpi](https://github.com/keilambda/ttfpi) | `ttfpi` | Copyright (c) 2024, thelissimus | `data/tentative/ttfpi.jsonl` |
| BSD-3-Clause | [Verified-zkEVM/zkLean](https://github.com/Verified-zkEVM/zkLean) | `zklean` | Copyright (c) 2026, Galois, Inc. | `data/tentative/zklean.jsonl` |
| MIT | [a2435191/lean-logic-formalization](https://github.com/a2435191/lean-logic-formalization) | `lean-logic-formalization` | Copyright (c) 2025 William Bradley | `data/tentative/lean-logic-formalization.jsonl` |
| MIT | [loganrjmurphy/LeanEuclid](https://github.com/loganrjmurphy/LeanEuclid) | `leaneuclid` | Copyright (c) 2024 Logan Murphy | `data/tentative/leaneuclid.jsonl` |
| MIT | [project-numina/LeanGeo](https://github.com/project-numina/LeanGeo) | `leangeo` | Copyright (c) 2024 Logan Murphy | `data/tentative/leangeo.jsonl` |
| MIT | [Robby955/FormalSLT](https://github.com/Robby955/FormalSLT) | `formalslt` | Copyright (c) 2026 Robby Sneiderman | `data/tentative/formalslt.jsonl` |
| MIT | [schildep/verified-3d-mesh-intersection](https://github.com/schildep/verified-3d-mesh-intersection) | `verified-3d-mesh-intersection` | Copyright (c) 2026 P Schilde | `data/tentative/verified-3d-mesh-intersection.jsonl` |
| MIT | [schildep/verified-polygon-intersection](https://github.com/schildep/verified-polygon-intersection) | `verified-polygon-intersection` | Copyright (c) 2026 P Schilde | `data/tentative/verified-polygon-intersection.jsonl` |
| MIT | [siqiliu-tsinghua/tautology](https://github.com/siqiliu-tsinghua/tautology) | `tautology` | Copyright (c) 2026 Si-Qi Liu | `data/tentative/tautology.jsonl` |
| MIT | [Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean) | `zkevm-clean` | Copyright (c) 2024-2025 zkSecurity, LLC | `data/tentative/zkevm-clean.jsonl` |
| MIT | [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm) | `evm-asm` | Copyright (c) 2026 ZkSecurity | `data/tentative/evm-asm.jsonl` |
| MIT | [vltanh/lean4-analysis-tao](https://github.com/vltanh/lean4-analysis-tao) | `lean4-analysis-tao` | Copyright (c) 2025 The-Anh Vu-Le | `data/tentative/lean4-analysis-tao.jsonl` |

Only permissively licensed libraries are registered. Copyleft material (GPL, AGPL, LGPL and the like)
cannot be compiled into one Apache-2.0 tree with everything else, so a source under such a licence is
not accepted.

## 3. Changes made to upstream material

As Apache-2.0 section 4(b) asks, the changes this repository makes to what it redistributes:

- **Seeded packages** (`scripts/seed.py`): files are moved to topic paths under `Tengoku/`; `import`
  lines, including module-system forms such as `public import`, are rewritten to the new module names;
  instance names Lean derives from the module root change their suffix from `_mathlib` to `_tengoku`;
  the root module `Tengoku.lean` gains a header comment and imports of the other seeded roots;
  ProofWidgets' demo modules are left out; `lakefile.toml` sets `maxSynthPendingDepth = 3`, as Mathlib's
  own lakefile does. Every seeded file that was changed says so in a line at its top, naming the package
  and commit it came from (`scripts/notices.py`); nothing else in a seeded file is edited.
- **Records** (`data/`): a statement and its proof are copied from the source file, with the context
  above it. Translated records are re-elaborated on this tree's toolchain, and an agent may rewrite
  the proof, or restate definitions without the source's notations, so that it compiles there.
- **Generated modules** (`Tengoku/<Library>/`, `scripts/generate.py`): records are wrapped in the
  library's namespace, their imports mapped onto the tree, corpus-only attributes stripped, and
  definitions shared by several records emitted once.

## 4. Removed sources

Earlier commits of this repository contained records from two copyleft libraries, removed because
their licences cannot be combined with the Apache-2.0 tree:

- `lean-wasm`: [T-Brick/lean-wasm](https://github.com/T-Brick/lean-wasm), GPL-3.0
- `software-foundations-lean`: [PnVDiscord/software-foundations-lean](https://github.com/PnVDiscord/software-foundations-lean), AGPL-3.0

Those copies remain in the git history under their upstream licences and are not covered by Apache-2.0.

## 5. Notices reproduced as their licences require

### MIT

Applies to lean4-cli and to every MIT library in section 2, each with its copyright line above.

```
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the
following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial
portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT
LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO
EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE
USE OR OTHER DEALINGS IN THE SOFTWARE.
```

### BSD 3-Clause

Applies to every BSD-3-Clause library in section 2, each with its copyright line above.

```
Redistribution and use in source and binary forms, with or without modification, are permitted provided
that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the
   following disclaimer.
2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and
   the following disclaimer in the documentation and/or other materials provided with the distribution.
3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or
   promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
```

## 6. The obligations these licences carry, and where each is met

| Obligation | Licence | Where it is met |
|---|---|---|
| State significant changes made to the software | Apache-2.0 | Section 3 above; a line at the top of every seeded file that was changed (`scripts/notices.py`) |
| Include the full text of the licence in modified software and in source or object copies | Apache-2.0, BSD-3-Clause, MIT | [LICENSE](LICENSE) is the full Apache-2.0 text; the full MIT and BSD 3-Clause texts are in section 5 |
| Retain the original copyright notices | Apache-2.0, BSD-3-Clause, MIT | Seeded files keep their upstream headers; each library's copyright line is in section 2; each record keeps its source's credit and names its source file at a fixed commit |
| Include the licence notice in all copies or substantial uses | MIT | Section 5, with the copyright line of each MIT library in section 2 |
| Include the `NOTICE` file's attribution notices when distributing | Apache-2.0 | [NOTICE](NOTICE), which reproduces the NOTICE files of `lean-pool` and `flt-anthropic` unchanged |

Two things to know about what is covered. `lean-pool` is itself an aggregate of other people's projects: most are
Apache-2.0, some MIT or relicensed by their authors, and its NOTICE (reproduced in [NOTICE](NOTICE)) names the
upstream repository and licence of every one of them. And the release assets carry the same three files, so a copy of
the data or of the compiled tree arrives with them: every monthly dataset release has `LICENSE`,
`LICENSE-THIRD-PARTY.md` and `NOTICE` among its files (attested like the dataset), and every nightly cache release
and the standing top-up release has them next to the compiled parts. Releases published before this change do not.

When a library is registered under a licence not listed here, add it to this file in the same pull request. If its
repository has a NOTICE file, reproduce that in [NOTICE](NOTICE) in the same pull request.
