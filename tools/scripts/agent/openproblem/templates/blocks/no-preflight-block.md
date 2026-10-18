
## No local preflight
The dev Makefile has no `preflight` target. Do not run `make preflight` and do not list its absence as an open reason or as a Verification row; the single required CI check `required` (workflow ci-current.yml), reported by `make pr-watch`, is the authority.
