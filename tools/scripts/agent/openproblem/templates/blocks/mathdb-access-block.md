
## MathDB access (binding prior-art check)
MathDB answers plain requests with a browser user agent. Run:
`curl -s -A "Mozilla/5.0" "https://mathdb.com/search?q=<title words or author>" | grep -o '/p/[0-9]*/[a-z0-9-]*' | sort -u`

Search with title words and author names; arXiv and OEIS numbers return noise. Then open every relevant hit with the same command (`curl -s -A "Mozilla/5.0" https://mathdb.com/p/<id>`) and read three things:
- the `Solutions N` count;
- the posted solution text;
- the `<time dateTime="…">` stamps (the first stamp is the posting, later ones are solutions).

MathDB often lists every numbered conjecture of a paper as a separate page (consecutive ids), so check the neighbouring ids too. A candidate whose page already carries a posted proof or counterexample is excluded, even if the page marks it unverified. Report the page ids and solution counts you read.
