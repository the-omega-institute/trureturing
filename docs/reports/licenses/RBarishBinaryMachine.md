# Binary machine supply

The finite binary single-tape model, stack-program algebra, compiler, simulation, numerical polynomial bounds and composition are licensed content from [RBarish-UTokyo/NPCompleteness-Lean4](https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925). The source revision is `3e603e795b44fedcf7d6dd65b7d1e30547ead925`. The full Apache-2.0 license is in `RBarishBinaryMachine-LICENSE.txt`; the immutable archive contains no NOTICE file. Source copyright notices, where present, remain in the corresponding source.

The immutable [source archive](https://codeload.github.com/RBarish-UTokyo/NPCompleteness-Lean4/tar.gz/3e603e795b44fedcf7d6dd65b7d1e30547ead925) has SHA-256 `1c0f46a8ccc32a190cf74266fa0ab81ed91263b7b7d2155cedfe677b7d614230`.

The upstream toolchain is `leanprover/lean4:v4.35.0-rc2`. The repository uses `leanprover/lean4:v4.33.0` and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Unequal toolchain pins rule out a package dependency. These are ordinary content ports; their original proof bodies are preserved. Adaptations add repository headers and provenance, and replace the module import prefix `Complexity` by `D5.S0.Computability.BinaryMachine`. The mathematical namespace remains `Complexity`. These supplied proofs carry no claim of new mathematical authorship.

## Replacement contract

At a change to this repository's own toolchain or mathlib pin, inspect that pinned dependency's compiled environment for the finite declaration set in each source module below. A replacement must supply the same finite local-instruction `Machine` semantics, initial binary tape, accepting/rejecting result, contiguous bit output, and uniform polynomial bounds. Candidate declaration types and their recursive definition dependencies must be definitionally equal after the explicit namespace renaming; a compiled Lean equivalence and transport may replace definitional equality. For each matched module, replace every live import and reference by the pinned declaration and remove the corresponding port and its mirror. A merely announced or unmerged upstream submission does not meet this contract. Absence of a match retains the ordinary port; no package, pin or compatibility layer is changed.

The finite declaration set is exactly the author-written declarations of the listed immutable modules, with their original qualified names. The original source hash identifies those names and types, making the presence, type comparison and transport checks decidable against this repository's installed pin. Removal is modulewise only when all its live declarations and downstream semantics are transported.

| Repository module | Original source | Original SHA-256 |
| --- | --- | --- |
| `BinaryMachine/Machine` | `Complexity/Machine.lean` | `9e2a577620b36abac6a312c8c63c91d46086bec3a3e0ce1744cd91672490ef41` |
| `BinaryMachine/StackMachine` | `Complexity/StackMachine.lean` | `3b73fabb61a95b032eea67b5414349f943f0dc909445d1333be9d3eeae9d9c26` |
| `BinaryMachine/StackProgram` | `Complexity/StackProgram.lean` | `beb3a101d59b39fa305c40debbf1e18755e0a841c188d2457f6bdecd5b56698c` |
| `BinaryMachine/StackCompiler` | `Complexity/StackCompiler.lean` | `d234cddf5c523b660aee5ef3b3bb8dcb5ce5068325608ad7e1aa41e243f1f698` |
| `BinaryMachine/TapeEquiv` | `Complexity/TapeEquiv.lean` | `5cde4fd1b96a8ec69f6355ba33dcf915969b525852efd243efdc358e188f3e12` |
| `BinaryMachine/StackPop` | `Complexity/StackPop.lean` | `2b0c1aab9964965d3b30be1367b731c41e13d61b2fc77dc8baf3244f9bbf6767` |
| `BinaryMachine/StackEncoding` | `Complexity/StackEncoding.lean` | `118ecb7ccd674a563185fda627a0b42c70dcf0d97a4bbebf2dd373b1cbb0515e` |
| `BinaryMachine/StackSimulation` | `Complexity/StackSimulation.lean` | `8b09665d32989ccbef3c4675af4bef5ed0e55e59d4f5f86dd203d43b77bde514` |
| `BinaryMachine/StackWords` | `Complexity/StackWords.lean` | `47112ad7b6800f78fde62821096db3bda4888948eda5b2ba475b27012d0eb6ac` |
| `BinaryMachine/TapeToStacks` | `Complexity/TapeToStacks.lean` | `b574b232a57fabe54d9183b552b8ee672447e1754e10a7b74386c4d0893755e6` |
| `BinaryMachine/Classes` | `Complexity/Classes.lean` | `b18405b1a7908525eba48d37cea9efb57d8938c81ae7562dcc1f2cbeca940ab5` |
| `BinaryMachine/Clock` | `Complexity/Clock.lean` | `6cad6280a44151f0a6fdf84cd06c52aacf664c207f7be3aebcfd354b78d95e9b` |
| `BinaryMachine/PolynomialBound` | `Complexity/PolynomialBound.lean` | `00ffd84a688e413e883bc43c152a5d802d141e92d6b05a536739e258273163d5` |
| `BinaryMachine/StackInit` | `Complexity/StackInit.lean` | `49f7d1d4018c3f247e0fdd531bb0206ae7ae3fcffd17079385b44bb736c1438c` |
| `BinaryMachine/StackCompile` | `Complexity/StackCompile.lean` | `470640ff7e2fa43e59164c1f5dba1b7e652b8260661d246235372c666482599f` |
| `BinaryMachine/Composition` | `Complexity/Composition.lean` | `f9d85502b0789772767afa5f87b80f0ec46e9c7a63ef1bd22c22155ab3e68912` |
| `BinaryMachine/Reductions` | `Complexity/Reductions.lean` | `ebbff88f92bf1a9656492bc5e83741ec9316f808f22821f1b24bde16b5d8a4f0` |

## Unary and pair decoding slice

`UnaryWords` retains only `SAT.Word`, `SAT.Parser`, `SAT.writeNat`, `SAT.readNat`, `SAT.readNat_writeNat`, `SAT.readNat_eq_some`, and `SATBounds.writeNat_length`. Their proof bodies are unchanged. `StackParse` imports this slice instead of the full SATBounds module; `StackPair` imports the original StackParse and Classes under their repository module names. These modules supply only the outer pair format and its primitive execution, not an alternate CNF format, SAT-completeness premise or Cook–Levin result. The replacement contract above includes exactly these seven declarations and all author-written declarations of StackParse and StackPair.

| Original source | Original SHA-256 |
| --- | --- |
| `Complexity/SAT.lean` | `56edf8fccc9aa9186b8f9ac1f5cec071e05be0c5999d22a1352d41e0851f890c` |
| `Complexity/SATBounds.lean` | `c728045b2b275c78b5349f799831b85c5b04e26ed74168afe2c0fcf294d6e91f` |
| `Complexity/StackParse.lean` | `d6d2d6a063be3515c740c77fcd287d700379879abf1d84c93bf821160cc69b04` |
| `Complexity/StackPair.lean` | `3b776d72b75b74fae2e2b07a191033da5106f8544f1c7f0c0eb61596cbd6acda` |
