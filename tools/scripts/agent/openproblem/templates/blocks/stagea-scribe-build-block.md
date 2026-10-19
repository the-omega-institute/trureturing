# Scribe build before mirror-ready (binding)

Before stopping with `mirror-ready`, build the Scribe project and run the Scribe corpus test (`FormulaCorpusInventoryTests`); both must exit 0. The Scribe SDK treats an unused private helper (`IDE0051`) as an error, which blocks `make emit` at Stage B. Delete every unused private `Formula` helper from the lane's `.scribe.cs` files.


- **Library note fields.** Write `doi:` as a bare DOI (`10.xxxx/...`), never as a URL; the Library parser rejects URLs. Run `make emit` before stopping, so that parser errors surface in Stage A.
