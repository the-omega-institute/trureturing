
## Library note locator (Scribe describe rule `incomplete-library-locator`)
Every `Library/**` note that a Scribe node cites must have a `## Verified locator` section after its frontmatter. The section body contains the frontmatter `doi:` value and the `url:` value verbatim, for example:

```
## Verified locator

DOI: https://doi.org/10.48550/arXiv.<id>

Source: https://arxiv.org/abs/<id>v1
```

Without it, `make gate` reports `describe red code=incomplete-library-locator`. Check: `grep -n '^## Verified locator' <note>`.

**Frontmatter `claim` is one line.** The Library loader rejects a folded or multi-line `claim:` (`field claim must be one canonical non-empty line`, from `make emit`). Write it as one line (quote it when it contains `:` or starts with a special character) and check that the YAML parses with each backslash surviving exactly once.
