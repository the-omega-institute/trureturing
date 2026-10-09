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
            Node("omega", "The cubic phase", Disp(Equal(Call("omega"),
                Call("exp", Div(Mul(Mul(D(2), Call("pi")), Call("I")), D(3))))),
                "The phase omega is the complex exponential of two pi times the imaginary unit divided by three.",
                "omega"),
            Node("weyl", "The qutrit Weyl operators", Disp(Equal(
                Call("W", K, L), Call("MatrixEntry", J, C,
                    Call("if", Equal(C, Add(J, L)), Pow(Call("omega"), Mul(Val(J), Val(K))), D(0))))),
                "For row j and column c, the Weyl operator W(k,l) has the cubic phase omega to j times k when c equals j+l, and is zero otherwise.",
                "W"),
            Node("bloch", "The Weyl--Bloch coefficient", Disp(Equal(
                Call("bloch", Rho, I, J, K, L), Call("trace", Mul(Rho,
                    Call("conjTranspose", Call("kronecker", Call("W", I, J), Call("W", K, L))))))),
                "The coefficient is the trace pairing of a two-qutrit matrix with the conjugate transpose of a tensor product of two Weyl operators.",
                "bloch"),
            Node("l1", "The entrywise one-norm", Disp(Equal(Call("l1", Rho),
                Sum(I, Sum(J, Sum(K, Sum(L, Norm(Call("bloch", Rho, I, J, K, L)))))))),
                "The quantity l1 is the sum of the complex norms of all 81 Weyl--Bloch coefficients.",
                "l1"),
            Node("density", "Finite density matrices", Disp(Iff(Call("IsDensity", Rho),
                And(Call("PosSemidef", Rho), Equal(Call("trace", Rho), D(1))))),
                "A density matrix is positive semidefinite and has trace one.", "IsDensity"),
            Node("separable", "Finite separable mixtures", Disp(Call("IsSeparable", Rho)),
                "A separable two-qutrit matrix is a finite convex mixture of tensor products of qutrit density matrices.",
                "IsSeparable"),
            Node("claim", "The sharp separable bound and an entangled violation", Disp(Call("claim")),
                "Every separable state has l1 at most 25, a separable state attains 25, and a normalized pure two-qutrit vector produces a Weyl--Bloch one-norm strictly above 25.",
                "claim")),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration) => Describe.Lean(
        DescribeId.Create("qutrit-weyl-l1-" + id), DeclarationHandle.Create(Prefix + declaration),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(F.Id(name)), [.. args]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) =>
        new Formula.Fraction(left, right);
    private static Formula Pow(Formula left, Formula right) =>
        new Formula.Power(left, right);
    private static Formula Sum(Formula index, Formula body) =>
        Seq(F.Sum, Sp, index, Sp, body);
    private static Formula Norm(Formula value) =>
        new Formula.Absolute(value);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula K => F.Id("k");
    private static Formula L => F.Id("l");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula C => F.Id("c");
    private static Formula Rho => F.Id("rho");
}
