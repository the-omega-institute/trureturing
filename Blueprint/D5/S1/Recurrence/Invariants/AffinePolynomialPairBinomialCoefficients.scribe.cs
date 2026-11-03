using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AffinePolynomialPairBinomialCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/werner2022a208509");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The affine polynomial pair has Werner's all-column binomial formula.",
        H("The affine polynomial pair of OEIS A208509"),
        Blocks(
            Paragraph(Text("The pair takes natural stages to pairs of polynomials in Z[X]. "
                + "The functions first and second select its polynomial components; coeff selects "
                + "a natural degree. The function natSub is truncated natural subtraction, "
                + "binomial is Nat.choose, and intCast casts a natural number to an integer. "
                + "Constants one and X in the defining equations are polynomials.")),
            Node("pair", "The actual affine polynomial recursion", PairFormula(),
                "Source index n>=1 corresponds to stage n-1: u(n,X)=first(pair(n-1)) "
                + "and v(n,X)=second(pair(n-1)). Thus u(1,X)=v(1,X)=1, and for every n>=2 "
                + "the source laws are u(n,X)=u(n-1,X)+X*v(n-1,X) and "
                + "v(n,X)=u(n-1,X)+v(n-1,X)+1. These are the laws in A208509 revision 28 "
                + "and its companion A208508 revision 10.", DescribeRole.Definition),
            Node("werner_a208509", "Werner's binomial coefficient formula", ResultFormula(),
                "The coefficient of X^k in the actual second polynomial equals the two "
                + "displayed integer binomial coefficients for every n>=1 and every k>=0. "
                + "There is no degree or column bound; zero tails are included. The n=0 "
                + "extension introduced by truncated subtraction is outside the conclusion. "
                + "Simultaneous induction proves the odd-binomial formula for the second "
                + "component and the even-binomial formula for the first component, with "
                + "the degree-zero correction subtracted from the latter. The odd step "
                + "uses both preceding components; the even step uses the shifted odd "
                + "component. Pascal identities normalize these coupled steps and cancel "
                + "the affine constant. The conjecture is attributed to Knud Werner, "
                + "Jan 11 2022; Clark Kimberling authored the OEIS entry. The bounded "
                + "supplier and literature screen establishes neither worldwide openness "
                + "nor publication priority. The distinct frozen JointPolynomialPairBinomialCoefficients "
                + "uses v_next=X*u+X*v and does not identify this affine second family.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create(
                    "oeis-a208509-affine-polynomial-pair-binomial-coefficients"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a208509-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula PairFormula()
    {
        Formula m = F.Id("m");
        Formula initial = And(Equal(First(D(0)), D(1)), Equal(Second(D(0)), D(1)));
        Formula step = All(m, And(
            Equal(First(Add(m, D(1))), Add(First(m), Mul(F.Id("X"), Second(m)))),
            Equal(Second(Add(m, D(1))), Add(Add(First(m), Second(m)), D(1)))));
        return Disp(new Formula.Aligned([initial, step]));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula degree = Add(Mul(D(2), k), D(1));
        return Disp(All(n, Implies(LessEqual(D(1), n), All(k,
            Equal(Call("coeff", Second(Call("natSub", n, D(1))), k),
                Add(Call("intCast", Call("binomial", Call("natSub", n, D(1)), degree)),
                    Call("intCast", Call("binomial", n, degree))))))));
    }

    private static Formula First(Formula m) => Call("first", Call("pair", m));
    private static Formula Second(Formula m) => Call("second", Call("pair", m));
    private static Formula All(Formula v, Formula body) =>
        Seq(Forall, Sp, v, Sp, InMacro, Sp, F.Id("Nat"), Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LessEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
