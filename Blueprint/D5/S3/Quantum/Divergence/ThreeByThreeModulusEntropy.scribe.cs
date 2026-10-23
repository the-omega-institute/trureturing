using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class ThreeByThreeModulusEntropyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entrywise modulus increases trace-log entropy for positive semidefinite three-by-three matrices.",
        H("Entropy under entrywise modulus in dimension three"), Blocks(
            Node("entropy_eq_spectrum", "Spectral trace-log formula", SpectrumFormula(),
                "Hermitian functional calculus expresses trace-log entropy as the sum over all real eigenvalues, with multiplicity."),
            Node("entryModulus", "Entrywise complex modulus", ModulusFormula(),
                "Matrix.map embeds the norm of every complex entry back into the complex numbers.", DescribeRole.Definition),
            Node("entryModulus_diag", "Diagonal entries are unchanged", MatrixInputs(All("i", Fin(D(3)),
                Imp(Psd(X("G")), Eq(App(Mod(X("G")), X("i"), X("i")), App(X("G"), X("i"), X("i")))))),
                "Positive semidefinite matrices have nonnegative real diagonal entries."),
            Node("entryModulus_trace", "Trace is unchanged", MatrixInputs(Imp(Psd(X("G")), Eq(Trace(Mod(X("G"))), Trace(X("G"))))),
                "The diagonal identity preserves the sum of diagonal entries."),
            Node("entryModulus_posSemidef", "Positivity in dimension three", MatrixInputs(Imp(Psd(X("G")), Psd(Mod(X("G"))))),
                "The first two elementary spectral coefficients are fixed and the determinant increases. Their nonnegativity excludes a negative eigenvalue."),
            Node("entryModulus_entropy_mono", "The modulus entropy inequality", MatrixInputs(Imp(Psd(X("G")), Le(TraceEntropy(X("G")), TraceEntropy(Mod(X("G")))))),
                "For three nonnegative eigenvalues with fixed mass and second elementary symmetric function, entropy increases with their product. Shifted logarithmic sums have ordered derivatives and equal limits at infinity. Entrywise modulus preserves the first two spectral coefficients and increases the determinant. No trace normalization or invertibility is required."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("modulus-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(F.Open, x, F.Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Mat(Formula n) => Call("Matrix", n, n, C);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula SumOver(string i, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(X(i), Colon, type), Sp, Parenthesized(body));
    private static Formula Re(Formula a) => App(Q("Complex", "re"), a);
    private static Formula Trace(Formula a) => App(Q("Matrix", "trace"), a);
    private static Formula Psd(Formula a) => App(Q("Matrix", "PosSemidef"), a);
    private static Formula Log(Formula a) => App(Q("CFC", "log"), a);
    private static Formula TraceEntropy(Formula a) => Negate(Re(Trace(Mul(a, Log(a)))));
    private static Formula Finite(string n, Formula body) => All(n, Q("Type"),
        Seq(OpenBracket, Call("Fintype", X(n)), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", X(n)), CloseBracket, Sp, body));

    private static Formula Mod(Formula g) => Call("entryModulus", g);
    private static Formula MatrixInputs(Formula body) => Disp(All("G", Mat(Fin(D(3))), body));
    private static Formula ModulusFormula() => MatrixInputs(
        Eq(Mod(X("G")), App(Q("Matrix", "map"), X("G"),
            Seq(X("fun"), Sp, Cast(X("z"), C), Sp, Mapsto, Sp,
                Cast(new Formula.Norm(X("z")), C)))));
    private static Formula SpectrumFormula()
    {
        var a = X("A");
        var eigen = App(Q("Matrix", "IsHermitian", "eigenvalues"), X("hA"), X("i"));
        return Disp(Finite("n", All("A", Mat(X("n")), All("hA", App(Q("Matrix", "IsHermitian"), a),
            Eq(TraceEntropy(a), Negate(SumOver("i", X("n"), Mul(eigen, App(Q("Real", "log"), eigen)))))))));
    }
}
