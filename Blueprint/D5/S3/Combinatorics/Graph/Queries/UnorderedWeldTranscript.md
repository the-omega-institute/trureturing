# Conditioning on a transcript of the welded graph

## Abstract

The conditional law of an alternating weld after complete neighborhood queries.

**Theorem 1.1 (A transcript specifies exactly the revealed weld edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/UnorderedWeldTranscript.weld_transcript_law`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/UnorderedWeldTranscript.weld_transcript_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embed a finite set of leaves into the vertex set of a fixed finite graph. There are n leaves of each color, with n at least two. The hidden weld is a uniform undirected alternating cycle on the leaves. A deterministic adaptive protocol queries complete unordered neighbor sets in the union graph.

Consider the transcript of a reference cycle disjoint in edges from the fixed graph. From all edges recorded in the transcript, remove the fixed edges and restrict to the leaves to obtain F. A candidate gives the same transcript exactly when it contains F. To compute the transcript probability, divide the completion count by half the product of n! and (n - 1)!. At positive transcript mass, the conditional law is uniform over those completions.

A replay must include each observed edge outside the fixed graph. Conversely, a candidate containing F supplies all observed edges after taking the union. Its degree after adding the fixed edges is bounded above by the reference degree because the reference adds two distinct edges outside the fixed graph per leaf and adds none at other vertices. Complete-neighborhood replay gives equality of the two transcripts.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/UnorderedWeldTranscript.weld_transcript_law`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/AlternatingUndirectedCompletionLaw](../LinearForests/AlternatingUndirectedCompletionLaw.md)
- Dependency: [D5/S3/Combinatorics/Graph/Queries/CompleteNeighborhoodHistory](CompleteNeighborhoodHistory.md)
