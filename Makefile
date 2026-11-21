SHELL := /bin/bash
.DEFAULT_GOAL := help
unexport NAMES

.PHONY: install-tools
install-tools:
	@python3 -I -B .github/scripts/install-tools.py

override release_goals := $(filter-out install-tools,$(or $(MAKECMDGOALS),help))
override release_args = $(foreach goal,$(release_goals),'$(subst ','"'"',$(goal))')
ifneq ($(release_goals),)
.PHONY: $(release_goals) dispatch-tools
$(release_goals): dispatch-tools ;

# Reject full cache builds without explicit confirmation before downloading tools.
ifneq ($(filter lean-cache-ensure,$(release_goals)),)
ifneq ($(origin FULL_BUILD):$(value FULL_BUILD),command line:1)
.PHONY: reject-full-cache
install-tools: | reject-full-cache
reject-full-cache:
	@echo 'full build requires explicit FULL_BUILD=1; use scoped targets instead' >&2; exit 2
endif
endif

# Match GNU Make's short option word, ignoring long flags and variable overrides.
ifneq ($(findstring n,$(filter-out -% %=%,$(firstword $(MAKEFLAGS)))),)
dispatch-tools:
	+@if [[ -f tools/consumer/Makefile ]]; then \
	    set -o pipefail; python3 -I -B .github/scripts/install-tools.py --read-makefile | \
	        $(MAKE) --no-print-directory -o install-tools -f - -- $(release_args); \
	else \
	    echo 'python3 -I -B .github/scripts/install-tools.py'; \
	    printf '%s' '$(MAKE) --no-print-directory -o install-tools -f tools/consumer/Makefile --'; printf ' %q' $(release_args); echo; \
	fi
else
dispatch-tools: | install-tools
	@$(MAKE) --no-print-directory -o install-tools -f tools/consumer/Makefile -- $(release_args)
endif
endif
