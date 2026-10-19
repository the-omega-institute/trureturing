
## No GPT Pro calls
Do not call `nyx.sh`, `nyxid oracle` or any ChatGPT Pro carrier: this session runs exactly one GPT Pro seat, owned by the orchestrator. Record any literature gap as `assumed_unverified` instead.

Fetching an access-restricted page or PDF (bot challenge, institutional block, failed direct request) through the NyxID Firecrawl proxy is allowed and expected before you record a literature gap: `nyxid proxy request api-firecrawl v1/scrape -m POST -H "Content-Type:application/json" -d '{"url":"<url>","formats":["markdown"]}' --output json`. Record the URL and the character count as the reading. Firecrawl does not open paid subscriptions.
