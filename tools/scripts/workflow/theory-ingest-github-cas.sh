# GitHub object creation and ref CAS helpers, sourced by theory-ingest-closure.sh.

github_create_object() {
  local endpoint="$1"
  local payload="$2"
  local output="$3"
  local token="${GITHUB_TOKEN:-}"
  local github_repository="${GITHUB_REPOSITORY:-}"
  local api_url="${GITHUB_API_URL:-https://api.github.com}"
  [[ -n "$token" && -n "$github_repository" ]] || fail \
    "GitHub object creation credentials are unavailable"
  local status
  status="$(curl --silent --show-error --location --request POST \
    --output "$output" --write-out '%{http_code}' \
    --header 'Accept: application/vnd.github+json' \
    --header "Authorization: Bearer $token" \
    --header 'X-GitHub-Api-Version: 2022-11-28' \
    --header 'Content-Type: application/json' \
    --data-binary "@$payload" \
    "$api_url/repos/$github_repository/git/$endpoint")" || fail \
      "GitHub object creation request failed: $endpoint"
  [[ "$status" == "201" ]] || fail \
    "GitHub object creation was rejected: $endpoint"
}

create_github_writeback_commit() {
  local repository="$1"
  local final_index="$2"
  local head_sha="$3"
  ensure_scratch
  local paths="$scratch_root/github-tree.$RANDOM.paths"
  local entries="$scratch_root/github-tree.$RANDOM.entries"
  GIT_INDEX_FILE="$final_index" git -C "$repository" diff --cached \
    --name-only -z "$head_sha" -- "${WRITE_PATHSPECS[@]}" > "$paths"
  : > "$entries"
  local path entry metadata mode object stage blob_bytes blob_payload blob_response remote_blob
  while IFS= read -r -d '' path; do
    entry="$(GIT_INDEX_FILE="$final_index" git -C "$repository" ls-files \
      --stage -- "$path")"
    metadata="${entry%%$'\t'*}"
    read -r mode object stage <<< "$metadata"
    [[ "$mode" == "100644" && "$stage" == "0" ]] || fail \
      "GitHub writeback tree contains a non-regular entry at $path"
    blob_bytes="$scratch_root/github-blob.$RANDOM.bytes"
    blob_payload="$scratch_root/github-blob.$RANDOM.payload.json"
    blob_response="$scratch_root/github-blob.$RANDOM.response.json"
    git -C "$repository" cat-file blob "$object" > "$blob_bytes"
    python3 - "$blob_bytes" "$blob_payload" <<'PY'
import base64
import json
import pathlib
import sys
content = base64.b64encode(pathlib.Path(sys.argv[1]).read_bytes()).decode("ascii")
pathlib.Path(sys.argv[2]).write_text(
    json.dumps({"content": content, "encoding": "base64"}, separators=(",", ":")) + "\n",
    encoding="ascii",
)
PY
    github_create_object "blobs" "$blob_payload" "$blob_response"
    remote_blob="$(python3 - "$blob_response" <<'PY'
import json
import pathlib
import sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")).get("sha")
if not isinstance(value, str):
    raise SystemExit(1)
print(value)
PY
)" || fail "GitHub blob response is malformed"
    [[ "$remote_blob" == "$object" ]] || fail \
      "GitHub blob address differs from the trusted writeback object"
    printf '%s\t%s\t%s\n' "$path" "$mode" "$remote_blob" >> "$entries"
  done < "$paths"
  [[ -s "$entries" ]] || fail "GitHub writeback commit has no changed entries"

  local tree_payload="$scratch_root/github-tree.$RANDOM.payload.json"
  local tree_response="$scratch_root/github-tree.$RANDOM.response.json"
  local base_tree_sha
  base_tree_sha="$(git -C "$repository" rev-parse "$head_sha^{tree}")"
  python3 - "$entries" "$tree_payload" "$base_tree_sha" <<'PY'
import json
import pathlib
import sys
entries = []
for line in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
    path, mode, sha = line.split("\t")
    entries.append({"path": path, "mode": mode, "type": "blob", "sha": sha})
pathlib.Path(sys.argv[2]).write_text(
    json.dumps({"base_tree": sys.argv[3], "tree": entries}, separators=(",", ":")) + "\n",
    encoding="ascii",
)
PY
  github_create_object "trees" "$tree_payload" "$tree_response"
  local tree_sha
  tree_sha="$(python3 - "$tree_response" <<'PY'
import json
import pathlib
import sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")).get("sha")
if not isinstance(value, str):
    raise SystemExit(1)
print(value)
PY
)" || fail "GitHub tree response is malformed"

  local commit_payload="$scratch_root/github-commit.$RANDOM.payload.json"
  local commit_response="$scratch_root/github-commit.$RANDOM.response.json"
  python3 - "$commit_payload" "$tree_sha" "$head_sha" <<'PY'
import json
import pathlib
import sys
document = {
    "message": "chore(digestion): auto-ingest theory update",
    "tree": sys.argv[2],
    "parents": [sys.argv[3]],
    "author": {
        "name": "theory-ingest-bot",
        "email": "theory-ingest-bot@users.noreply.github.com",
    },
    "committer": {
        "name": "theory-ingest-bot",
        "email": "theory-ingest-bot@users.noreply.github.com",
    },
}
pathlib.Path(sys.argv[1]).write_text(
    json.dumps(document, separators=(",", ":")) + "\n",
    encoding="ascii",
)
PY
  github_create_object "commits" "$commit_payload" "$commit_response"
  local values
  values="$(python3 - "$commit_response" <<'PY'
import json
import pathlib
import sys
document = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
sha = document.get("sha")
parents = document.get("parents")
if not isinstance(sha, str) or not isinstance(parents, list):
    raise SystemExit(1)
print(sha)
print(" ".join(parent.get("sha", "") for parent in parents if isinstance(parent, dict)))
PY
)" || fail "GitHub commit response is malformed"
  local remote_commit parents
  remote_commit="${values%%$'\n'*}"
  parents="${values#*$'\n'}"
  [[ -n "$remote_commit" && "$parents" == "$head_sha" ]] || fail \
    "GitHub writeback commit does not have exactly the event head as parent"
  GITHUB_REMOTE_COMMIT_SHA="$remote_commit"
}

atomic_update_github_ref() {
  local remote_ref="$1"
  local expected_sha="$2"
  local new_sha="$3"
  local token="${GITHUB_TOKEN:-}"
  local github_repository="${GITHUB_REPOSITORY:-}"
  local graphql_url="${GITHUB_GRAPHQL_URL:-https://api.github.com/graphql}"
  [[ -n "$token" && -n "$github_repository" && -n "$graphql_url" ]] || fail \
    "GitHub compare-and-swap credentials are unavailable"
  ensure_scratch
  local repository_payload="$scratch_root/github-repository.$RANDOM.payload.json"
  local repository_body="$scratch_root/github-repository.$RANDOM.response.json"
  local update_payload="$scratch_root/github-ref.$RANDOM.payload.json"
  local update_body="$scratch_root/github-ref.$RANDOM.response.json"
  python3 - "$repository_payload" "$github_repository" <<'PY'
import json
import pathlib
import sys
owner, name = sys.argv[2].split("/", 1)
document = {
    "query": "query($owner:String!,$name:String!){repository(owner:$owner,name:$name){id}}",
    "variables": {"owner": owner, "name": name},
}
pathlib.Path(sys.argv[1]).write_text(
    json.dumps(document, separators=(",", ":")) + "\n",
    encoding="ascii",
)
PY
  local status
  status="$(curl --silent --show-error --location --request POST \
    --output "$repository_body" --write-out '%{http_code}' \
    --header 'Accept: application/vnd.github+json' \
    --header "Authorization: Bearer $token" \
    --header 'Content-Type: application/json' \
    --data-binary "@$repository_payload" \
    "$graphql_url")" || fail "cannot resolve the GitHub repository node"
  [[ "$status" == "200" ]] || fail "cannot resolve the GitHub repository node"
  local repository_id
  repository_id="$(python3 - "$repository_body" <<'PY'
import json
import pathlib
import sys
document = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
value = document.get("data", {}).get("repository", {}).get("id")
if document.get("errors") or not isinstance(value, str) or not value:
    raise SystemExit(1)
print(value)
PY
)" || fail "cannot resolve the GitHub repository node"

  python3 - \
      "$update_payload" "$repository_id" "$remote_ref" "$expected_sha" "$new_sha" <<'PY'
import json
import pathlib
import sys
mutation_id = "theory-ingest-" + sys.argv[5]
document = {
    "query": "mutation($input:UpdateRefsInput!){updateRefs(input:$input){clientMutationId}}",
    "variables": {
        "input": {
            "repositoryId": sys.argv[2],
            "refUpdates": [{
                "name": sys.argv[3],
                "beforeOid": sys.argv[4],
                "afterOid": sys.argv[5],
                "force": False,
            }],
            "clientMutationId": mutation_id,
        },
    },
}
pathlib.Path(sys.argv[1]).write_text(
    json.dumps(document, separators=(",", ":")) + "\n",
    encoding="ascii",
)
PY
  status="$(curl --silent --show-error --location --request POST \
    --output "$update_body" --write-out '%{http_code}' \
    --header 'Accept: application/vnd.github+json' \
    --header "Authorization: Bearer $token" \
    --header 'Content-Type: application/json' \
    --data-binary "@$update_payload" \
    "$graphql_url")" || fail \
      "GitHub compare-and-swap ref update failed"
  [[ "$status" == "200" ]] || fail "remote head changed before atomic update"
  python3 - "$update_body" "$new_sha" <<'PY' || fail \
    "remote head changed before atomic update"
import json
import pathlib
import sys
document = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
value = document.get("data", {}).get("updateRefs", {}).get("clientMutationId")
if document.get("errors") or value != "theory-ingest-" + sys.argv[2]:
    raise SystemExit(1)
PY
}
