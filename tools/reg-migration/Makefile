.PHONY: lean parse extract test test-parser

LEAN_TARGETS ?= ExtractInputs ParseSources

lean:
	@/bin/bash ../scripts/worktree/lean-cache-run.sh lake -d tools/reg-migration build $(LEAN_TARGETS)

test:
	@python3 -m unittest discover -s tests -v

test-parser:
	@REG_MIGRATION_PARSER="$(abspath ../../.lake/build/reg-migration/bin/regMigrationParse)" /bin/bash ../scripts/worktree/lean-cache-run.sh lake -d tools/reg-migration env python3 -m unittest discover -s tools/reg-migration/tests -p test_parser.py -v

parse:
	@test -n "$(MANIFEST)" -a -n "$(OUTPUT)" || { echo 'MANIFEST and OUTPUT are required' >&2; exit 2; }
	@/bin/bash ../scripts/worktree/lean-cache-run.sh lake -d tools/reg-migration build regMigrationParse
	@/bin/bash ../scripts/worktree/lean-cache-run.sh lake -d tools/reg-migration env "$(abspath ../../.lake/build/reg-migration/bin/regMigrationParse)" --manifest "$(MANIFEST)" "$(OUTPUT)"

extract:
	@test -n "$(MANIFEST)" -a -n "$(OUTPUT)" || { echo 'MANIFEST and OUTPUT are required' >&2; exit 2; }
	@/bin/bash ../scripts/worktree/lean-cache-run.sh lake -d tools/reg-migration build regMigrationExtract
	@/bin/bash ../scripts/worktree/lean-cache-run.sh lake -d tools/reg-migration env "$(abspath ../../.lake/build/reg-migration/bin/regMigrationExtract)" --manifest "$(MANIFEST)" "$(OUTPUT)"
