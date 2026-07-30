#!/usr/bin/env bash

HOST_CONTRACT_SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
HOST_CONTRACT_SCHEMA="$HOST_CONTRACT_SCRIPT_DIR/../host-contract.schema"
HOST_CONTRACT_NAMES=()
HOST_CONTRACT_TYPES=()
HOST_CONTRACT_REQUIRED=()
HOST_CONTRACT_SOURCES=()
HOST_CONTRACT_SEEN=()

host_contract_error() {
  printf 'host-contract: %s\n' "$*" >&2
  return 2
}

host_contract_trim() {
  local value="$1"
  value="${value#"${value%%[![:space:]]*}"}"
  value="${value%"${value##*[![:space:]]}"}"
  printf '%s' "$value"
}

host_contract_index() {
  local wanted="$1" index
  index=0
  while [[ "$index" -lt "${#HOST_CONTRACT_NAMES[@]}" ]]; do
    if [[ "${HOST_CONTRACT_NAMES[$index]}" == "$wanted" ]]; then
      printf '%s\n' "$index"
      return 0
    fi
    index=$((index + 1))
  done
  return 1
}

host_contract_load_schema() {
  local line line_number=0 version_seen=0 name type required source
  HOST_CONTRACT_NAMES=()
  HOST_CONTRACT_TYPES=()
  HOST_CONTRACT_REQUIRED=()
  HOST_CONTRACT_SOURCES=()
  HOST_CONTRACT_SEEN=()
  [[ -f "$HOST_CONTRACT_SCHEMA" ]] \
    || { host_contract_error "schema is missing: $HOST_CONTRACT_SCHEMA"; return; }

  while IFS= read -r line || [[ -n "$line" ]]; do
    line_number=$((line_number + 1))
    line="$(host_contract_trim "$line")"
    [[ -z "$line" || "$line" == \#* ]] && continue
    if [[ "$version_seen" == "0" ]]; then
      [[ "$line" == "schema_version|1" ]] \
        || { host_contract_error "$HOST_CONTRACT_SCHEMA:$line_number: schema_version must be 1"; return; }
      version_seen=1
      continue
    fi

    IFS='|' read -r name type required source <<EOF
$line
EOF
    [[ -n "$name" && -n "$type" && -n "$required" && -n "$source" \
        && "$line" == "$name|$type|$required|$source" ]] \
      || { host_contract_error "$HOST_CONTRACT_SCHEMA:$line_number: invalid schema row"; return; }
    [[ "$name" =~ ^[A-Z][A-Z0-9_]*$ ]] \
      || { host_contract_error "$HOST_CONTRACT_SCHEMA:$line_number: invalid key $name"; return; }
    case "$type" in
      absolute_path|boolean|command|identity|identity_list|label|label_prefix|path_list|positive_integer|repository) ;;
      *) host_contract_error "$HOST_CONTRACT_SCHEMA:$line_number: unknown type $type"; return ;;
    esac
    [[ "$required" == "true" || "$required" == "false" ]] \
      || { host_contract_error "$HOST_CONTRACT_SCHEMA:$line_number: required must be true or false"; return; }
    [[ "$source" == "host" || "$source" == "repository" ]] \
      || { host_contract_error "$HOST_CONTRACT_SCHEMA:$line_number: source must be host or repository"; return; }
    ! host_contract_index "$name" >/dev/null 2>&1 \
      || { host_contract_error "$HOST_CONTRACT_SCHEMA:$line_number: duplicate key $name"; return; }
    HOST_CONTRACT_NAMES[${#HOST_CONTRACT_NAMES[@]}]="$name"
    HOST_CONTRACT_TYPES[${#HOST_CONTRACT_TYPES[@]}]="$type"
    HOST_CONTRACT_REQUIRED[${#HOST_CONTRACT_REQUIRED[@]}]="$required"
    HOST_CONTRACT_SOURCES[${#HOST_CONTRACT_SOURCES[@]}]="$source"
    HOST_CONTRACT_SEEN[${#HOST_CONTRACT_SEEN[@]}]=0
  done < "$HOST_CONTRACT_SCHEMA"
  [[ "$version_seen" == "1" && "${#HOST_CONTRACT_NAMES[@]}" -gt 0 ]] \
    || { host_contract_error "$HOST_CONTRACT_SCHEMA: schema has no declarations"; return; }
}

host_contract_parse_value() {
  local raw="$1" file="$2" line_number="$3" value
  if [[ "$raw" =~ ^\"([^\"\$\`\\]*)\"[[:space:]]*(#.*)?$ ]]; then
    value="${BASH_REMATCH[1]}"
  elif [[ "$raw" =~ ^([A-Za-z0-9_./,:@%+=-]+)[[:space:]]*(#.*)?$ ]]; then
    value="${BASH_REMATCH[1]}"
  else
    host_contract_error "$file:$line_number: invalid data line"
    return
  fi
  printf '%s' "$value"
}

host_contract_validate_value() {
  local name="$1" type="$2" value="$3" item old_ifs
  case "$type" in
    absolute_path)
      [[ "$value" == /* && "$value" != "/" && "$value" != *"/../"* \
          && "$value" != */.. && "$value" != *"//"* ]]
      ;;
    boolean)
      [[ "$value" == "0" || "$value" == "1" ]]
      ;;
    command)
      [[ "$value" =~ ^[A-Za-z0-9][A-Za-z0-9\ ./_-]*$ ]]
      ;;
    identity)
      [[ "$value" =~ ^[A-Za-z0-9][A-Za-z0-9._/-]*$ ]]
      ;;
    identity_list)
      old_ifs="$IFS"
      IFS=','
      for item in $value; do
        [[ "$item" =~ ^[A-Za-z0-9][A-Za-z0-9._/-]*$ ]] \
          || { IFS="$old_ifs"; return 1; }
      done
      IFS="$old_ifs"
      [[ -n "$value" && "$value" != *, && "$value" != ,* && "$value" != *,,* ]]
      ;;
    label)
      [[ "$value" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]]
      ;;
    label_prefix)
      [[ "$value" =~ ^[A-Za-z0-9][A-Za-z0-9._:-]*$ ]]
      ;;
    path_list)
      old_ifs="$IFS"
      IFS=':'
      for item in $value; do
        [[ "$item" == /* && "$item" != "/" && "$item" != *"/../"* \
            && "$item" != */.. && "$item" != *"//"* ]] \
          || { IFS="$old_ifs"; return 1; }
      done
      IFS="$old_ifs"
      [[ -n "$value" && "$value" != *: && "$value" != :* && "$value" != *::* ]]
      ;;
    positive_integer)
      [[ "$value" =~ ^[1-9][0-9]*$ ]]
      ;;
    repository)
      [[ "$value" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]]
      ;;
    *) return 1 ;;
  esac || {
    host_contract_error "$name must have type $type"
    return
  }
}

host_contract_parse_file() {
  local file="$1" source="$2" allow_include="$3"
  local line trimmed line_number=0 key raw value index include_seen=0
  [[ -f "$file" ]] || { host_contract_error "configuration is missing: $file"; return; }

  while IFS= read -r line || [[ -n "$line" ]]; do
    line_number=$((line_number + 1))
    trimmed="$(host_contract_trim "$line")"
    [[ -z "$trimmed" || "$trimmed" == \#* ]] && continue
    if [[ "$allow_include" == "true" \
        && "$trimmed" == 'source "$FKST_HOST_ROOT/.fkst/deploy.env"' ]]; then
      [[ "$include_seen" == "0" ]] \
        || { host_contract_error "$file:$line_number: duplicate repository include"; return; }
      include_seen=1
      continue
    fi

    if [[ "$trimmed" =~ ^(export[[:space:]]+)?([A-Z][A-Z0-9_]*)=(.*)$ ]]; then
      key="${BASH_REMATCH[2]}"
      raw="${BASH_REMATCH[3]}"
    else
      host_contract_error "$file:$line_number: invalid data line"
      return
    fi
    value="$(host_contract_parse_value "$raw" "$file" "$line_number")" || return
    index="$(host_contract_index "$key")" \
      || { host_contract_error "$file:$line_number: undeclared key $key"; return; }
    [[ "${HOST_CONTRACT_SOURCES[$index]}" == "$source" ]] \
      || { host_contract_error "$file:$line_number: $key belongs to ${HOST_CONTRACT_SOURCES[$index]} data"; return; }
    [[ "${HOST_CONTRACT_SEEN[$index]}" == "0" ]] \
      || { host_contract_error "$file:$line_number: duplicate key $key"; return; }
    [[ -n "$value" ]] \
      || { host_contract_error "$file:$line_number: $key must not be empty"; return; }
    host_contract_validate_value "$key" "${HOST_CONTRACT_TYPES[$index]}" "$value" || return
    printf -v "$key" '%s' "$value"
    export "$key"
    HOST_CONTRACT_SEEN[$index]=1
  done < "$file"

  if [[ "$allow_include" == "true" && "$include_seen" != "1" ]]; then
    host_contract_error "$file: missing repository data include"
    return
  fi
}

host_contract_load() {
  local host_config="$1" repository_config index
  [[ -n "$host_config" ]] || { host_contract_error "host config path is required"; return; }
  [[ "$host_config" == /* ]] \
    || { host_contract_error "host config path must be absolute"; return; }
  host_config="$(cd -- "$(dirname -- "$host_config")" 2>/dev/null && pwd -P)/$(basename -- "$host_config")" \
    || { host_contract_error "cannot canonicalize host config: $host_config"; return; }

  host_contract_load_schema || return
  host_contract_parse_file "$host_config" host true || return
  # The schema and the repository data it governs must come from the same checkout.
  repository_config="$HOST_CONTRACT_SCRIPT_DIR/../deploy.env"
  host_contract_parse_file "$repository_config" repository false || return

  index=0
  while [[ "$index" -lt "${#HOST_CONTRACT_NAMES[@]}" ]]; do
    if [[ "${HOST_CONTRACT_REQUIRED[$index]}" == "true" \
        && "${HOST_CONTRACT_SEEN[$index]}" != "1" ]]; then
      host_contract_error "required ${HOST_CONTRACT_SOURCES[$index]} key ${HOST_CONTRACT_NAMES[$index]} is unset"
      return
    fi
    index=$((index + 1))
  done
  HOST_CONFIG="$host_config"
  export HOST_CONFIG
}
