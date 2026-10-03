using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class FiniteTranslationStabilizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/FiniteTranslationStabilizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite translation stabilizers act freely on their stabilized sets.",
        H("Finite Translation Stabilizers"),
        Blocks(
            Paragraph(Text("Let S be a finite subset of an additive commutative group G. "
                + "Its translation stabilizer H consists of the elements t for which t+S=S. "
                + "The cardinality statements require G to be finite.")),
            Node("card_nsmul_eq_zero_of_vadd_finset_eq", "The cardinal annihilates a stabilizer",
                Disp(Seq(Call("translate", T(), S()), Sp, Eq, Sp, S(), Sp, Implies, Sp,
                    Call("card", S()), T(), Sp, Eq, Sp, D(0))),
                "Summing all translated points gives |S|t+sum(S)=sum(S), so |S|t=0. "
                + "This conclusion also applies when the ambient group is infinite."),
            Node("stabilizer_card_dvd_card", "Stabilizer order divides set size",
                Disp(Seq(Call("card", Hset()), Sp, Mid, Sp, Call("card", S()))),
                "H acts freely on S: a translation fixing one point is zero. "
                + "Partitioning S into H-orbits proves the divisibility."),
            Node("eq_stabilizer_coset_of_card_eq", "Maximal stabilizers give cosets",
                Disp(Seq(Call("card", Hset()), Sp, Eq, Sp, Call("card", S()),
                    Comma, Sp, P(), Sp, InMacro, Sp, S(), Sp, Implies, Sp,
                    S(), Sp, Eq, Sp, P(), Sp, Plus, Sp, Hset())),
                "The orbit of p lies in S, and translation makes its points distinct. "
                + "Equal finite cardinalities make the orbit all of S."),
            Node("three_point_eq_stabilizer_coset", "Three-point stabilizer cosets",
                Disp(Seq(Call("card", S()), Sp, Eq, Sp, D(3), Comma, Sp,
                    T(), Sp, InMacro, Sp, Hset(), Comma, Sp, T(), Sp, Neq, Sp, D(0),
                    Comma, Sp, P(), Sp, InMacro, Sp, S(), Sp, Implies, Sp,
                    S(), Sp, Eq, Sp, P(), Sp, Plus, Sp, Hset())),
                "A nonzero member rules out stabilizer order one. Since the order divides "
                + "three, it equals three, and S is the coset through any p in S."),
            Node("three_point_eq_translation_cycle", "The full translation cycle",
                Disp(Seq(Call("card", S()), Sp, Eq, Sp, D(3), Comma, Sp,
                    Call("translate", T(), S()), Sp, Eq, Sp, S(), Comma, Sp,
                    T(), Sp, Neq, Sp, D(0), Comma, Sp, P(), Sp, InMacro, Sp, S(),
                    Sp, Implies, Sp,
                    S(), Sp, Eq, Sp, OpenBrace, P(), Comma, Sp, P(), Sp, Plus, Sp, T(),
                    Comma, Sp, P(), Sp, Plus, Sp, D(2), T(), CloseBrace)),
                "Translation by t moves p around three distinct points and then returns "
                + "to p. These points exhaust S."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("translation-stabilizer-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula S() => F.Id("S");
    private static Formula T() => F.Id("t");
    private static Formula P() => F.Id("p");
    private static Formula Hset() => F.Id("H");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
