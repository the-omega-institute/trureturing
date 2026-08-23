using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class SimpleToPGroupTrivialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every homomorphism from the alternating group A5 to a finite p-group is trivial.",
        H("Triviality of Homomorphisms from A5 to Finite P-Groups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("alternating-five-hom-to-p-group-is-trivial"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/PrimePowers/SimpleToPGroupTrivial."
                    + "alternating_five_hom_to_pgroup_trivial"),
                H("Every homomorphism from A5 to a finite p-group is trivial"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a prime p and a finite p-group P. Every group homomorphism from the "
                        + "alternating group A5 to P sends every element to the identity. Thus the "
                        + "trivial homomorphism is the only such map, uniformly in the prime and "
                        + "the target p-group.")),
                    Paragraph(Text(
                        "The kernel is normal in the simple group A5, so it is either the identity "
                        + "subgroup or all of A5. An identity kernel would make the homomorphism "
                        + "injective and transfer the p-group structure of the target to A5. That "
                        + "would make A5 nilpotent, hence solvable and therefore commutative by "
                        + "simplicity, contradicting the noncommutativity of the alternating group "
                        + "of degree five. The kernel must therefore be all of A5, which makes the "
                        + "homomorphism trivial."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula alternatingFive = new Formula.Subscript(F.Id("A"), D(5));

        return Disp(Seq(
            Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Sp, Rightarrow, Sp,
            Forall, Sp, F.Id("P"), Comma, Sp,
            Open,
            Operatorname, Grp(F.Id("FiniteGroup")), Open, F.Id("P"), Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("IsPGroup")), Open,
            F.Id("p"), Comma, Sp, F.Id("P"), Close,
            Close, Sp, Rightarrow, Sp,
            Forall, Sp, F.Id("phi"), Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("Hom")), Open,
            alternatingFive, Comma, Sp, F.Id("P"), Close, Comma, Sp,
            Forall, Sp, F.Id("g"), Sp, InMacro, Sp, alternatingFive, Comma, Sp,
            F.Id("phi"), Open, F.Id("g"), Close, Sp, Eq, Sp, D(1)));
    }
}
