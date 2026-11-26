using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class PairSumStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/PairSumStability.";
    private static readonly LibraryNoteRef ComposedAddition = LibraryNoteRef.Create("D5/L/Zeros/brawleycarlitz1987composed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pair-sum resultant converts half-plane stability to integer coefficient signs.",
        H("Pair sums of polynomial roots"),
        Blocks(
            Node("definition", "sumResultant", "Pair-sum resultant",
                Seq(Call(F.Id("r"), F.Id("T")), Eq, Call(Seq(Operatorname, Grp(F.Id("Res")), Underscore, Grp(F.Id("Y"))),
                    Call(F.Id("p"), F.Id("Y")), Call(F.Id("p"), Seq(F.Id("T"), Minus, F.Id("Y"))))),
                "Use Y as the eliminated variable and T as the coefficient variable. Both degree parameters are the degree of p.",
                DescribeRole.Definition),
            Node("roots", "eval2_sumResultant_eq_zero_iff", "Roots are pair sums",
                Seq(Val("r", "z"), Eq, D(0), Iff, Exists, Sp, F.Id("u"), Comma, F.Id("v"), Comma, Sp,
                    Par(Seq(Val("p", "u"), Eq, D(0), Land, Val("p", "v"), Eq, D(0), Land,
                        F.Id("u"), Plus, F.Id("v"), Eq, F.Id("z")))),
                "For a nonzero polynomial and an injective coefficient map to the complex numbers, evaluation commutes with the Sylvester determinant. Its product formula permits equal roots in the pair.",
                DescribeRole.Theorem),
            Node("degree", "sumResultant_degree_leading", "Degree and leading coefficient",
                Seq(Op("deg", "r"), Eq, Pow(F.Id("d"), D(2)), Land,
                    Op("lc", "r"), Eq, Pow(F.Id("a"), Seq(D(2), F.Id("d")))),
                "Under an injective coefficient map to the complex numbers, let d be the degree of the nonzero input and a its leading coefficient. The product of the d translated factors has degree d², with another factor a^d from the resultant formula.",
                DescribeRole.Theorem),
            Node("closed", "closed_iff_sumResultant_coeff_nonneg", "Closed stability",
                Seq(Stable(Le), Iff, Par(Scan())),
                "Here p has integer coefficients and positive leading coefficient. Real linear factors and conjugate quadratics give nonnegative coefficients for a closed-stable resultant. Any root of p with positive real part pairs with its conjugate to give a positive real resultant root, which the coefficient signs exclude.",
                DescribeRole.Theorem),
            Node("strict", "strict_iff_sumResultant_coeff_nonneg", "Strict stability",
                Seq(Stable(Lt), Iff, Par(Seq(Par(Scan()), Land, D(0), Lt, Coeff(D(0))))),
                "For integer p with positive leading coefficient, the same scan and a positive constant coefficient exclude pair sums equal to zero. An imaginary-axis root of p pairs with its conjugate at zero.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("pair-sum-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(ComposedAddition),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Par(Formula content) => Seq(Open, content, Close);
    private static Formula Pow(Formula bas, Formula exponent) => Seq(bas, Caret, Grp(exponent));
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Val(string p, string z) => Call(F.Id(p), F.Id(z));
    private static Formula Op(string name, string argument) => Call(Seq(Operatorname, Grp(F.Id(name))), F.Id(argument));
    private static Formula Coeff(Formula index) => Seq(OpenBracket, Pow(F.Id("T"), index), CloseBracket, F.Id("r"));
    private static Formula Stable(Formula relation) =>
        Par(Seq(Forall, Sp, F.Id("z"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
            Val("p", "z"), Eq, D(0), Implies, Re, Sp, F.Id("z"), relation, D(0)));
    private static Formula Scan() =>
        Seq(Forall, Sp, D(0), Le, F.Id("j"), Le, Pow(Op("deg", "p"), D(2)), Comma, Sp, D(0), Le, Coeff(F.Id("j")));
}
