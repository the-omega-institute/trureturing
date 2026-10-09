using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class QutritWeylBlochNormSeparableBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/sutter2026grouptheoretic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-qutrit Weyl--Bloch entrywise one-norm is bounded by 25 on separable states.",
        H("The qutrit Weyl--Bloch one-norm"),
        Blocks(
            Node("weyl", "The qutrit Weyl operators", Disp(
                All("k", FinThree, All("l", FinThree, All("j", FinThree, All("c", FinThree,
                    Equal(Call("W", K, L, J, C), Call("if", Equal(C, Add(J, L)),
                        Pow(Call("omega"), Mul(Val(J), Val(K))), D(0)))))))),
                "For row j and column c, W(k,l) has the cubic phase omega to j times k when c equals j+l modulo three, and is zero otherwise. omega denotes D5.S3.QuantumContext.HesseSicCertificate.omega: the complex exponential of two pi times the imaginary unit divided by three.", Prefix + "W"),
            Node("bloch", "The Weyl--Bloch coefficient", Disp(
                All("rho", JointMatrix, All("i", FinThree, All("j", FinThree,
                    All("k", FinThree, All("l", FinThree, Equal(Call("bloch", Rho, I, J, K, L),
                        Call("trace", Mul(Rho, Call("conjTranspose",
                            Call("kronecker", Call("W", I, J), Call("W", K, L)))))))))))),
                "The coefficient is the trace pairing with the conjugate transpose of a tensor product of two Weyl operators.", Prefix + "bloch"),
            Node("l1", "The entrywise one-norm", Disp(All("rho", JointMatrix,
                Equal(Call("l1", Rho), Sum(I, FinThree, Sum(J, FinThree,
                    Sum(K, FinThree, Sum(L, FinThree, Norm(Call("bloch", Rho, I, J, K, L))))))))),
                "The quantity l1 is the sum of the complex norms of all 81 Weyl--Bloch coefficients.", Prefix + "l1"),
            Node("separable", "Finite separable mixtures", Disp(All("rho", JointMatrix,
                Iff(Call("IsSeparable", Rho), SeparableFormula()))),
                "A separable two-qutrit matrix is a finite convex mixture of tensor products of qutrit density matrices. IsDensity denotes D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity: positive semidefinite with trace one.", Prefix + "IsSeparable"),
            Node("claim", "The sharp separable bound and an entangled violation",
                Disp(Iff(Call("claim"), ClaimFormula())),
                "Every separable state has l1 at most 25, a separable state attains 25, and a normalized pure two-qutrit vector produces a Weyl--Bloch one-norm strictly above 25.", Prefix + "claim"),
            Describe.Lean(DescribeId.Create("qutrit-weyl-l1-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The sharp separable bound"), StatementSource.FromAuthor(Disp(Call("claim"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every qutrit density matrix, the squared Weyl coefficients sum to at most three. The identity coefficient is one, leaving a squared sum at most two over the other eight coefficients. Cauchy--Schwarz bounds their sum of moduli by four. The local one-norm is therefore at most five.")),
                    Paragraph(Text("Weyl coefficients factor on tensor products. The product one-norm is at most twenty-five, and convexity preserves this bound for every finite separable mixture.")),
                    Paragraph(Text("The vector (0,1,-1)/sqrt(2) gives a qutrit density matrix with local one-norm five; its tensor square attains twenty-five. The normalized two-qutrit vector (2|00>+|02>+|11>-|20>)/sqrt(7) has one-norm (169+2sqrt(13))/7, which exceeds twenty-five. Thus the separable threshold is sharp and its strict violation detects entanglement."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sutter-popp-hiesmayr-2025-qutrit-weyl-bloch-norm-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration) => Describe.Lean(
        DescribeId.Create("qutrit-weyl-l1-" + id), DeclarationHandle.Create(declaration),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula FinThree => Call("Fin", D(3));
    private static Formula JointIndex => Call("Prod", FinThree, FinThree);
    private static Formula MatrixType(Formula index) => Call("Matrix", index, index, Call("Complex"));
    private static Formula JointMatrix => MatrixType(JointIndex);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula SeparableFormula()
    {
        var n = F.Id("n"); var t = F.Id("t"); var p = F.Id("p");
        var sigma = F.Id("sigma"); var tau = F.Id("tau");
        var fin = Call("Fin", n); var family = Arrow(fin, MatrixType(FinThree));
        var pt = new Formula.Apply(p, [t]);
        var st = new Formula.Apply(sigma, [t]); var tt = new Formula.Apply(tau, [t]);
        return ExistsOne("n", Call("Nat"), ExistsOne("p", Arrow(fin, Call("Real")),
            ExistsOne("sigma", family, ExistsOne("tau", family,
                And(All("t", fin, Le(D(0), pt)),
                    And(Equal(Sum(t, fin, pt), D(1)),
                        And(All("t", fin, And(Call("IsDensity", st), Call("IsDensity", tt))),
                            Equal(Rho, Sum(t, fin, Call("smul", Call("ofReal", pt),
                                Call("kronecker", st, tt)))))))))));
    }

    private static Formula ClaimFormula()
    {
        var psi = F.Id("psi");
        return And(All("rho", JointMatrix, Imp(Call("IsSeparable", Rho), Le(Call("l1", Rho), D(2,5)))),
            And(ExistsOne("rho", JointMatrix,
                    And(Call("IsSeparable", Rho), Equal(Call("l1", Rho), D(2,5)))),
                ExistsOne("psi", Arrow(JointIndex, Call("Complex")),
                    And(Equal(Call("dotProduct", Call("star", psi), psi), D(1)),
                        Lt(D(2,5), Call("l1", Call("vecMulVec", psi, Call("star", psi))))))));
    }

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(F.Id(name)), [.. args]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(left, right);
    private static Formula Sum(Formula index, Formula type, Formula body) =>
        Seq(F.Sum, Underscore, Grp(index, Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Norm(Formula value) => new Formula.Absolute(value);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula K => F.Id("k");
    private static Formula L => F.Id("l");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula C => F.Id("c");
    private static Formula Rho => F.Id("rho");
}
