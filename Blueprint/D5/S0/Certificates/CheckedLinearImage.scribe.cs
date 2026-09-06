using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class CheckedLinearImageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/Certificates/CheckedLinearImage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Executable rational certificates determine complete real query images.",
        H("Checked Linear Query Images"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("checked-real-query-image"),
                DeclarationHandle.Create(Module + "checked_real_query_image"),
                H("Accepted endpoint data determine every real target"),
                StatementSource.FromAuthor(ImageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "C and V are arbitrary finite types, including empty types. A is a rational "
                        + "C-by-V matrix, b is a rational C-vector, c is a rational V-vector, and p "
                        + "is a RawSharpPayload C V. The only additional premise is that checkSharp "
                        + "accepts these exact inputs.")),
                    Paragraph(Text(
                        "The payload contains two rational endpoint values, two rational primal "
                        + "vectors, and two rational multiplier vectors, with no proof fields. "
                        + "The checker tests multiplier nonnegativity, column identities for c and "
                        + "minus c, weighted right-hand-side bounds, both primal feasibility "
                        + "conditions, and both objective equalities.")),
                    Paragraph(Text(
                        "RealQueryImage(A,b,c) denotes the set of sums of c(j)x(j), after casting "
                        + "rational coefficients to the reals, for all real vectors x satisfying "
                        + "every cast row inequality. The theorem includes irrational targets and "
                        + "coincident endpoints. No separate convexity or nonemptiness hypothesis "
                        + "is imposed: mathlib's convex halfspaces and linear images supply it.")),
                    Paragraph(Text(
                        "The underlying checked_query_image theorem works over any field K with "
                        + "a linear order and IsStrictOrderedRing K. This is certificate soundness, "
                        + "not an optimizer or a certificate-existence theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("checked-ordered-field-infeasible"),
                DeclarationHandle.Create(Module + "checked_infeasible"),
                H("Accepted Farkas data exclude all field-valued solutions"),
                StatementSource.FromAuthor(InfeasibleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "K is a field with a linear order and IsStrictOrderedRing K; C and V are "
                        + "arbitrary finite types. A, b, and y have rational entries. checkFarkas "
                        + "requires nonnegative y, zero weighted coefficients in every column, "
                        + "and a strictly negative weighted right-hand side.")),
                    Paragraph(Text(
                        "FeasibleK(A,b,x) means that, for every row i, the sum of the cast "
                        + "coefficient A(i,j) times x(j) is at most the cast b(i). Acceptance "
                        + "excludes every such K-valued x. The rational companion theorem "
                        + "constructs the existing RationalFarkas.Certificate and invokes "
                        + "RationalFarkas.infeasible_of_certificate."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula C => F.Id("C");
    private static Formula V => F.Id("V");
    private static Formula A => F.Id("A");
    private static Formula B => F.Id("b");
    private static Formula Objective => F.Id("c");
    private static Formula P => F.Id("p");

    private static Formula FiniteTypes() => Seq(
        Forall, Sp, C, Comma, V, Comma, Sp,
        Call("Fintype", C), Land, Call("Fintype", V), Sp, Rightarrow);

    private static Formula RationalSystem() => Seq(
        Forall, Sp, A, Colon, C, To, V, To, Q, Comma, Sp,
        B, Colon, C, To, Q, Comma);

    private static Formula ImageFormula() => Disp(new Formula.Aligned([
        Seq(FiniteTypes(), Sp, RationalSystem(), Sp,
            Objective, Colon, V, To, Q, Comma, Sp,
            P, Colon, Call("RawSharpPayload", C, V), Comma),
        Seq(Call("checkSharp", A, B, Objective, P), Eq, F.Id("true"), Sp, Rightarrow),
        Seq(Call("RealQueryImage", A, B, Objective), Eq,
            Call("Icc", Call("castReal", Call("lower", P)),
                Call("castReal", Call("upper", P))), Dot)
    ]));

    private static Formula InfeasibleFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("K"), Comma, Sp, Call("Field", F.Id("K")), Land,
            Call("LinearOrder", F.Id("K")), Land,
            Call("IsStrictOrderedRing", F.Id("K")), Sp, Rightarrow),
        Seq(FiniteTypes(), Sp, RationalSystem(), Sp,
            F.Id("y"), Colon, C, To, Q, Comma),
        Seq(Call("checkFarkas", A, B, F.Id("y")), Eq, F.Id("true"), Sp, Rightarrow,
            Neg, Exists, Sp, F.Id("x"), Colon, V, To, F.Id("K"), Comma, Sp,
            Call("FeasibleK", A, B, F.Id("x")), Dot)
    ]));
}
