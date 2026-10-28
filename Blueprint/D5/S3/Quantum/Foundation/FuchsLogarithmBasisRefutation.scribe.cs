using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FuchsLogarithmBasisRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/fuchs1996thesislogarithmbasis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful qutrit pair refutes a physical-basis diagonalization of Fuchs's logarithm argument.",
        H("Fuchs's physical-basis logarithm question is false"),
        Blocks(
            Paragraph(Text(
                "Fuchs asks in §3.5.3 whether a basis can make the matrix in the logarithm of equation (3.244) diagonal. "
                    + "The construction below uses the Kronecker sum from equation (3.237), the inverse of the continuous-functional-calculus square root, and unitary conjugation.")),
            Describe.Lean(
                DescribeId.Create("fuchs-kronecker-sum"),
                DeclarationHandle.Create(Prefix + "ksum"),
                H("The Kronecker sum"),
                StatementSource.FromAuthor(Disp(KsumFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a complex square matrix X indexed by Fin d, ksum X is the sum of the identity tensor X and the entrywise-starred X tensor the identity. "
                        + "This is the operator form of Fuchs's Kronecker sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fuchs-logarithm-argument"),
                DeclarationHandle.Create(Prefix + "logArg"),
                H("The matrix in the logarithm"),
                StatementSource.FromAuthor(Disp(LogArgFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "logArg is the identity plus t times the conjugated Kronecker difference, with both conjugations given by the inverse of the continuous-functional-calculus square root of ksum rho0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fuchs-physical-basis-question"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The physical-basis diagonalization question"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Fuchs's source sentence is: \"An interesting open question is whether there exists a basis in which to represent the operators ρ̂₀, ρ̂₁, etc., so that the matrix appearing in the logarithm above is diagonal. If so, this would greatly simply the computation of L(t).\" (after equation (3.244), §3.5.3, pp. 77–78). "
                        + "The Lean proposition asks for a unitary basis change for every positive-definite trace-one pair with invertible difference and every t in (0,1]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fuchs-qutrit-rho0"),
                DeclarationHandle.Create(Prefix + "rho0"),
                H("The diagonal qutrit state"),
                StatementSource.FromAuthor(Disp(Equal(
                    Typed(Local("rho0"), MatrixType(FinOf(D(3)))),
                    Apply(Q("Matrix", "diagonal"), Seq(Bang, OpenBracket,
                        Typed(new Formula.Fraction(D(1), D(2)), Complexes()), Comma, Sp,
                        new Formula.Fraction(D(1), D(3)), Comma, Sp,
                        new Formula.Fraction(D(1), D(6)), CloseBracket))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "rho0 is the complex three-by-three diagonal matrix with entries 1/2, 1/3 and 1/6."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fuchs-qutrit-rho0-positive-definite"),
                DeclarationHandle.Create(Prefix + "rho0_posDef"),
                H("The qutrit state is positive definite"),
                StatementSource.FromAuthor(Disp(Apply(Q("Matrix", "PosDef"), Local("rho0")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every diagonal entry of rho0 is strictly positive, so rho0 is positive definite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fuchs-qutrit-rho0-trace-one"),
                DeclarationHandle.Create(Prefix + "rho0_trace"),
                H("The qutrit state has trace one"),
                StatementSource.FromAuthor(Disp(Equal(Apply(Q("Matrix", "trace"), Local("rho0")), D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The diagonal entries of rho0 sum to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fuchs-physical-basis-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The qutrit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take rho0 = diag(1/2,1/3,1/6) and rho1 = (1/16)[[7,-1,0],[-1,5,0],[0,0,4]]. Both matrices are positive definite with trace one, and the determinant of rho1-rho0 is -1/4608.")),
                    Paragraph(Text(
                        "The -1/4 eigenspace of the normalized Kronecker difference is the line through the vectorization of M = [[1,sqrt(5/6),0],[sqrt(5/6),sqrt(2/3),0],[0,0,0]]. Its upper-left two-by-two minor is sqrt(2/3)-5/6, which is nonzero. Every column induced by a physical unitary has zero value for that minor, so no physical unitary conjugation makes the logarithm argument diagonal.")),
                    Paragraph(Text(
                        "Thus the source's universal basis question is refuted by a faithful noncommuting qutrit pair. Arbitrary unitary diagonalization on the enlarged tensor space and the commuting sufficient case remain separate statements."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fuchs-1996-thesis-logarithm-basis-question"),
                    ResolutionKind.Refuted)))));

    private static Formula KsumFormula()
    {
        Formula i = FinOf(V("d"));
        Formula x = V("X");
        Formula one = Typed(D(1), MatrixType(i));
        Formula tensorLeft = Tensor(one, x);
        Formula tensorRight = Tensor(Apply(Q("Matrix", "map"), x, Q("star")), one);
        return All("d", Naturals(), All("X", MatrixType(i),
            Equal(Apply(Local("ksum"), x), Add(tensorLeft, tensorRight))));
    }

    private static Formula LogArgFormula()
    {
        Formula i = FinOf(V("d"));
        Formula pair = Product(i, i);
        Formula matrix = MatrixType(pair);
        Formula rho0 = V("rho0");
        Formula rho1 = V("rho1");
        Formula t = V("t");
        Formula root = Apply(Q("CFC", "sqrt"), Apply(Local("ksum"), rho0));
        Formula sandwich = Multiply(Multiply(Inverse(root),
            Apply(Local("ksum"), Subtract(rho1, rho0))), Inverse(root));
        return All("d", Naturals(), All("rho0", MatrixType(i), All("rho1", MatrixType(i),
            All("t", Reals(), Equal(Apply(Local("logArg"), rho0, rho1, t),
                Add(Typed(D(1), matrix), Smul(Cast(t, Complexes()), sandwich)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula i = FinOf(V("d"));
        Formula matrices = MatrixType(i);
        Formula rho0 = V("rho0");
        Formula rho1 = V("rho1");
        Formula t = V("t");
        Formula transformed = Apply(Local("logArg"),
            Multiply(Multiply(Star(V("U")), rho0), V("U")),
            Multiply(Multiply(Star(V("U")), rho1), V("U")), t);
        Formula witness = ExistsQ("U", MatrixType(i),
            And(Member(V("U"), Apply(Q("Matrix", "unitaryGroup"), i, Complexes())),
                Apply(Q("Matrix", "IsDiag"), transformed)));
        Formula hypotheses = Imp(Apply(Q("Matrix", "PosDef"), rho0),
            Imp(Apply(Q("Matrix", "PosDef"), rho1),
            Imp(Equal(Apply(Q("Matrix", "trace"), rho0), D(1)),
            Imp(Equal(Apply(Q("Matrix", "trace"), rho1), D(1)),
            Imp(Neq(Apply(Q("Matrix", "det"), Subtract(rho1, rho0)), D(0)),
                All("t", Reals(), Imp(Lt(D(0), t), Imp(Le(t, D(1)), witness))))))));
        return All("d", Naturals(), All("rho0", matrices, All("rho1", matrices, hypotheses)));
    }

    private static Formula Local(string name) => Q("D5", "S3", "Quantum", "Foundation", "FuchsLogarithmBasisRefutation", name);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (string part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula MatrixType(Formula i) => Apply(Q("Matrix"), i, i, Complexes());
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula ExistsQ(string name, Formula type, Formula body) =>
        Seq(FormulaDsl.Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Equal(Formula a, Formula b) => Eq(a, b);
    private static Formula Neq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Star(Formula x) => Apply(Q("star"), x);
    private static Formula Inverse(Formula x) => new Formula.Power(Parenthesized(x), Seq(Minus, D(1)));
    private static Formula Tensor(Formula a, Formula b) => Apply(Q("Matrix", "kroneckerMap"), Multiplication(), a, b);
    private static Formula Multiplication() => Lambda("x", Complexes(), Lambda("y", Complexes(), Multiply(V("x"), V("y"))));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
}
