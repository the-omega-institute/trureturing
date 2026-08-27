# Vendored KaTeX

`katex.min.js` is the renderer the published site runs on, kept in-tree so the Blueprint
markdown gate parses formulas with the real parser instead of a hand-maintained
approximation of it, offline and at a version pinned by these bytes.

| | |
| --- | --- |
| Upstream | https://github.com/KaTeX/KaTeX |
| Version | 0.16.22 |
| Source | `https://cdn.jsdelivr.net/npm/katex@0.16.22/dist/katex.min.js` |
| sha256 | `e8d885505949f3a5f4abdd5dd0d53696bd1371ad26ffbf4f310dcd77c8cdae89` |
| Licence | MIT, reproduced verbatim in `LICENSE` |

Only the parser is exercised: the gate calls `katex.renderToString` with
`throwOnError` and keeps the verdict, never the HTML. Fonts, stylesheets and the
browser bundle are therefore not vendored.

The gate itself runs on the change: `make test` routes a Blueprint delta through
`scribe-content-checks.sh`, which hands `markdown-check` the paths the change touched.

Raising the version means replacing both files, updating the table above, and running the
gate over the whole corpus once — a stricter KaTeX release can turn formulas red that the
previous one accepted, and those documents are not in the diff that raises it:

```sh
find Blueprint -name '*.md' -print0 |
  dotnet run --project tools/StrataLint.Scribe --configuration Release -- \
    markdown-check --report .lake/build/stratalint/raw-lean-report.json --paths-from -
```
