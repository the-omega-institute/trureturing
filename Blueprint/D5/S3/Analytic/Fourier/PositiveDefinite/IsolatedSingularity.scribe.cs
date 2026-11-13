using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier.PositiveDefinite;

internal sealed class IsolatedSingularityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict translation Gram positivity from an isolated singularity",
        H("An isolated failure of a linear increment bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("isolated-singularity-strict-gram"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/PositiveDefinite/IsolatedSingularity.posDef_of_isolated_non_lipschitz"),
                H("Strict positivity on every finite distinct configuration"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let k be a complex valued function on a normed additive commutative group V. Assume that for every natural number m and every map x from Fin m to V, the matrix with entry k(x_j-x_i) is positive semidefinite. At every nonzero base point r assume the increment k(r+h)-k(r) is O(h) as h tends to zero. At zero assume k(h)-k(0) is not O(h). Equivalently, at each nonzero r there are finite constants C_r and delta_r>0 such that norm(k(r+h)-k(r))<=C_r*norm(h) whenever norm(h)<delta_r, whereas no such constants exist at zero. The constants may depend on r. No continuity assumption is imposed.")),
                    Paragraph(Text("For every natural number n and every injective map x from Fin n to V, the matrix with entry k(x_j-x_i) is positive definite over the complex numbers. Thus its Hermitian quadratic form is strictly positive on every nonzero complex coefficient vector. The empty configuration is included; the assertion there is vacuous. There is no diameter restriction.")),
                    Paragraph(Text("To prove the conclusion, take a vector c in the kernel of the finite Gram matrix and append an arbitrary node t. Extend c by a zero coordinate. Its quadratic form for the augmented positive semidefinite Gram matrix is zero. The positive semidefinite null-vector identity therefore makes the entire augmented matrix-vector product zero. In particular its new row gives sum_i k(x_i-t)*c_i=0 for every t in V, including repeated nodes.")),
                    Paragraph(Text("If c is nonzero, choose j with c_j nonzero. Subtract the translate relation at t=x_j from the relation at t=x_j-h. The j term is c_j*(k(h)-k(0)); each other term is c_i*(k(x_i-x_j+h)-k(x_i-x_j)). Injectivity gives x_i-x_j nonzero for i different from j. Finite sums and constant multiplication preserve the O(h) bounds, and division by the nonzero coefficient c_j forces the forbidden O(h) bound at zero. Hence the matrix has trivial kernel; positive semidefiniteness then gives positive definiteness."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula p, Formula q) =>
        new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula Claim()
    {
        Formula v = F.Id("V"), k = F.Id("k"), r = F.Id("r"), h = F.Id("h"),
            n = F.Id("n"), m = F.Id("m"), x = F.Id("x"), y = F.Id("y");
        Formula nat = Seq(Mathbb, Grp(F.Id("N"))), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula map(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
        Formula gram(Formula z) => Seq(F.Id("i"), Comma, Sp, F.Id("j"), Sp, Mapsto, Sp,
            At(k, Subtract(At(z, F.Id("j")), At(z, F.Id("i")))));
        Formula bound(Formula a) => Call("IsBigO", Call("nhds", D(0)),
            Seq(h, Sp, Mapsto, Sp, Subtract(At(k, Add(a, h)), At(k, a))),
            Seq(h, Sp, Mapsto, Sp, h));
        Formula positive = All("m", nat, All("y", map(Call("Fin", m), v),
            Call("PosSemidef", gram(y))));
        Formula regular = All("r", v, Imp(new Formula.Relation(r,
            FormulaRelationOperator.NotEqual, D(0)), bound(r)));
        Formula singular = Seq(Neg, Sp, bound(D(0)));
        Formula strict = All("n", nat, All("x", map(Call("Fin", n), v),
            Imp(Call("Injective", x), Call("PosDef", gram(x)))));
        return Disp(All("V", Seq(Operatorname, Grp(F.Id("Type"))), Seq(
            OpenBracket, Call("NormedAddCommGroup", v), CloseBracket, Comma, Sp,
            All("k", map(v, complex), Imp(positive, Imp(regular, Imp(singular, strict)))))));
    }
}
