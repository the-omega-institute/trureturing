using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CompactRootCoherenceDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);

    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);

    private static Formula IffF(Formula left, Formula right) =>
        Seq(Grp(left), Sp, Iff, Sp, Grp(right));

    private static Formula Statement()
    {
        Formula hType = V("H");
        Formula rational = Seq(Mathbb, Grp(F.Id("Q")));
        Formula multiplicativeQ = Call("Multiplicative", rational);
        Formula homType = Call("MonoidHom", multiplicativeQ, hType);
        Formula one = D(1);
        Formula n = V("n");
        Formula x = V("x");
        Formula phi = V("phi");
        Formula h = V("h");
        Formula rootClause = Seq(
            Forall, Sp, n, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            D(0), Sp, Lt, Sp, n, Sp, Rightarrow, Sp,
            Exists, Sp, x, Colon, Sp, hType, Comma, Sp,
            Seq(x, Caret, Grp(n)), Sp, Eq, Sp, h);
        Formula homClause = Seq(
            Exists, Sp, phi, Colon, Sp, homType, Comma, Sp,
            Call("phi", Call("ofAdd", one)), Sp, Eq, Sp, h);
        return Disp(Seq(
            All("H", Call("Type", V("u"))),
            Inst("Group", hType),
            Inst("TopologicalSpace", hType),
            Inst("IsTopologicalGroup", hType),
            Inst("T2Space", hType),
            Inst("CompactSpace", hType),
            All("h", hType),
            IffF(rootClause, homClause), Dot));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compactness turns separate positive roots into one coherent rational homomorphism.",
        H("Compact Root Coherence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-all-positive-roots-iff-exists-rat-hom"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/CompactRootCoherence."
                        + "exists_all_positive_roots_iff_exists_rat_hom"),
                H("Positive roots and rational homomorphisms are equivalent"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary compact Hausdorff topological group H and h in H, "
                            + "the existence of a positive n-th root of h for every positive "
                            + "natural n is equivalent to one algebraic homomorphism from the "
                            + "additive rationals, represented as Multiplicative Q, sending "
                            + "additive rational one to h, that is, phi(ofAdd(1:Q)) = h.")),
                    Paragraph(Text(
                        "The forward direction puts all H-valued functions indexed by Q into the "
                            + "compact product H^Q. Each finite set of rational coordinates "
                            + "has a nonempty closed constraint set: a single D-th root of h "
                            + "supplies the values, and denominator clearing makes the finite "
                            + "addition equations hold inside its cyclic subgroup. Compactness "
                            + "then supplies a point in every finite constraint set, which is "
                            + "a global homomorphism. Hausdorffness is used for the closed "
                            + "equalizers.")),
                    Paragraph(Text(
                        "The reverse direction uses the root phi(ofAdd(1/n)) "
                            + "and applies its power map. No topology on Q, continuity, "
                            + "connectedness, Lie structure, faithfulness, or commutativity of "
                            + "H is asserted."))),
                DescribeRole.Theorem))));
}
