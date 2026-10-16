using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StoneCech;

internal sealed class FreeUltrafilterCardinalityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/StoneCech/FreeUltrafilterCardinality.";

    private static Formula Statement => Disp(Seq(
        new Formula.Power(Num(2), FormulaDsl.Id("c")), Sp, Le, Sp,
        Call("Card", FormulaDsl.Id("FreeUF"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite traces construct an independent family whose Boolean assignments inject into the free ultrafilters on the naturals.",
        H("Classical cardinal supply of free ultrafilters"),
        Blocks(
            Paragraph(Text(
                "Here c is Cardinal.continuum, namely two to the power aleph-zero, and Card is Cardinal.mk. "
                + "FreeUF denotes exactly the subtype {u : Ultrafilter Nat // (u : Filter Nat) <= Filter.cofinite}. "
                + "The filter order reverses inclusion of collections of sets, so this condition says that u contains every cofinite set. "
                + "On the naturals these are the free, nonprincipal ultrafilters. All cardinal powers and inequalities in the statement are cardinal operations. "
                + "The public statement is closed: it has no supplied independent family, cardinal-supply premise, topology instance or selection hypothesis.")),
            Describe.Lean(
                DescribeId.Create("two-to-continuum-free-ultrafilters"),
                DeclarationHandle.Create(Owner + "continuum_power_le_mk_freeUltrafilter_nat"),
                H("At least two-to-continuum free ultrafilters"),
                StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Topology/frolik1960countablycompact")),
                Blocks(
                    Paragraph(Text(
                        "The construction starts on Code = Nat times Finset (Finset Nat). A code (n,F) consists of a natural number "
                        + "and a finite collection of finite subsets of the naturals. For A contained in Nat, trace(n,A) is A intersected with the initial segment below n, "
                        + "represented as a Finset. Define family(A) to contain exactly those (n,F) for which trace(n,A) belongs to F. "
                        + "These objects and the intermediate lemmas are private, consumed parts of this proof.")),
                    Paragraph(Text(
                        "Distinct subsets A and B differ at some natural k. For every n greater than k their traces differ, since membership of k is visible in both traces. "
                        + "There are only finitely many pairs in any finite collection s of subsets, so eventually trace(n,-) is injective on all of s simultaneously.")),
                    Paragraph(Text(
                        "A Boolean assignment is an arbitrary T contained in Set Nat. For finite s contained in Set Nat, pattern(V,T,s) consists of the x such that, "
                        + "for every A in s, x belongs to V(A) exactly when A belongs to T. Choose N beyond the simultaneous trace-separation threshold. "
                        + "For each t, use the code (N+t,F_t), where F_t is the image under trace(N+t,-) of the A in s that belong to T. "
                        + "Trace injectivity prevents an unselected A in s from sharing a selected trace. Thus every such code realizes the whole finite pattern. "
                        + "Their distinct first coordinates make the pattern infinite, including when s is empty.")),
                    Paragraph(Text(
                        "The countable coding type has the injective encoding Encodable.encode' Code into Nat. Take natFamily(A) to be the image of family(A) under this encoding. "
                        + "Injectivity both preserves infinitude and recovers membership in each family(A), so all finite Boolean patterns of natFamily remain infinite subsets of Nat.")),
                    Paragraph(Text(
                        "For any family V with this infinite-pattern property and any assignment T, let F(s) be cofinite inf principal(pattern(V,T,s)). "
                        + "An infinite pattern meets every cofinite set, hence each F(s) is nonbottom. The union s union t refines both constraints, "
                        + "so these filters are directed in the refinement order and their infimum f is nonbottom. Ultrafilter.of f extends this actual filter. "
                        + "The resulting u contains all cofinite sets and all singleton-index patterns. A positive singleton pattern puts V(i) in u; "
                        + "a negative one puts its complement in u, excluding V(i). Consequently V(i) belongs to u exactly when i belongs to T.")),
                    Paragraph(Text(
                        "Apply this extension to natFamily and choose one realizing free ultrafilter u(T) for every T : Set (Set Nat). "
                        + "If u(T)=u(R), membership of natFamily(A) recovers, for every A : Set Nat, the equivalence A in T if and only if A in R. "
                        + "Set extensionality therefore gives T=R. This is an injection of all subsets of Set Nat into FreeUF. "
                        + "Cardinal.mk_le_of_injective gives the cardinal comparison; mk_set, mk_nat and two_power_aleph0 identify its domain cardinal as exactly two to the power c. "
                        + "The public result is the lower bound 2^c <= Card(FreeUF); it does not state the matching upper bound or a cardinal equality.")),
                    Paragraph(Text(
                        "The proof uses classical logic and choice: Ultrafilter.of supplies the ultrafilter extension, and choose selects a realizing ultrafilter for every assignment. "
                        + "It is an explicit finite-trace construction of the independent family, followed by classical filter extension and witness selection, "
                        + "rather than an effective enumeration of ultrafilters. Neither an independent family nor a ready-made supply of free ultrafilters is assumed.")),
                    Paragraph(Text(
                        "Frolik's proof of Lemma 2.8 explicitly invokes Pospisil's theorem that the Stone-Cech compactification of a countably infinite discrete space has cardinal 2^c. "
                        + "The cited canonical Library note records that attribution and its precise hypotheses on printed pages 333-334. "
                        + "It attests the classical cardinal-supply result; it does not attribute this exact finite-trace implementation to Frolik. "
                        + "The original Pospisil and Katetov sources were not independently read. This is general mathematical infrastructure, with no novelty claim.")),
                    Paragraph(Text(
                        "A later construction may use this supply when comparing a continuum-sized forbidden family with available ultrafilters. "
                        + "Distinct ultrafilters alone do not give distinct projected cluster values, and this theorem supplies no section-goodness property or section-dense seed. "
                        + "The later section-good selector, its fresh projected values, the required space and graph construction, and the original Question 1 remain separate obligations."))),
                DescribeRole.Theorem))));
}
