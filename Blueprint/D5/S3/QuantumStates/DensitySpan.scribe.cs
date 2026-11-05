using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class DensitySpanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density matrices span the real Hermitian matrix space in every finite dimension.",
        H("Density span"),
        Blocks(
            Describe.Lean(DescribeId.Create("density-span-tomographically-complete"),
                DeclarationHandle.Create(Prefix + "TomographicallyComplete"), H("Tomographic completeness"),
                StatementSource.FromAuthor(Disp(TomographicFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every member of a tomographically complete set is positive semidefinite with trace one, and its real span is the Hermitian matrix space."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("density-span-all-density"),
                DeclarationHandle.Create(Prefix + "all_density_tomographically_complete"), H("All density matrices are tomographically complete"),
                StatementSource.FromAuthor(Disp(AllDensityFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In every natural dimension, including dimension zero, the set of positive semidefinite trace-one matrices spans the real Hermitian operator space."))),
                DescribeRole.Theorem)),
        []));

    private static Formula V(string name) => F.Id(name);
    private static Formula Field(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string x, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Mat(Formula d) => Call("Matrix", Fin(d), Fin(d), Field("C"));
    private static Formula Set(Formula type) => Call("Set", type);
    private static Formula Trace(Formula a) => Call("tr", a);
    private static Formula D(long n) => FormulaDsl.D(n);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);

    private static Formula TomographicFormula()
    {
        Formula d = V("d"), t = V("T"), rho = V("rho");
        return All("d", Field("N"), All("T", Set(Mat(d)),
            new Formula.Relation(Call("TomographicallyComplete", t), FormulaRelationOperator.Iff,
                Parenthesized(And(
                    All("rho", Mat(d), new Formula.Logic(Parenthesized(Mem(rho, t)), FormulaLogicOperator.Implies,
                        Parenthesized(And(Call("PosSemidef", rho), Eq(Trace(rho), D(1)))))),
                    Eq(Call("span", Field("R"), t), Call("HermitianSpace", d)))))));
    }

    private static Formula AllDensityFormula()
    {
        Formula d = V("d"), rho = V("rho");
        Formula density = And(Call("PosSemidef", rho), Eq(Trace(rho), D(1)));
        Formula densities = Seq(OpenBrace, rho, Sp, Colon, Sp, Mat(d), Sp, Bar, Sp, density, CloseBrace);
        return All("d", Field("N"), Call("TomographicallyComplete", densities));
    }
}
