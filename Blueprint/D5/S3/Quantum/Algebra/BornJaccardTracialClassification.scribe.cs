using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class BornJaccardTracialClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Born-weighted Jaccard distances on all complex subspaces are metrics exactly for tracial states.",
        H("Born-weighted Jaccard tracial classification"),
        Blocks(Describe.Lean(
            DescribeId.Create("born-jaccard-tracial-classification"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/BornJaccardTracialClassification."
                + "tracial_classification"),
            H("Full subspace classification and faithful separation"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let n be any integer at least two, H the usual complex Euclidean "
                    + "space of dimension n, rho any positive-definite Hermitian matrix of trace one, "
                    + "and c any nonnegative real number. All subspaces, projections and traces use "
                    + "this same H and rho. Write P(X) for the ordinary orthogonal projection onto X, "
                    + "mu(X)=Re Tr(rho P(X)), and f(X)=c+mu(X). The trace pairing is real. Join is "
                    + "the actual linear sum and meet is intersection. The distance d(X,Z) is "
                    + "1-f(X intersect Z)/f(X+Z) whenever its denominator is nonzero, and zero "
                    + "when the denominator vanishes. Faithfulness makes this last case exactly "
                    + "c=0 and X=Z=0.")),
                Paragraph(Text("The displayed Tri means the triangle inequality for every ordered "
                    + "triple of actual subspaces. The displayed Metric means that a MetricSpace "
                    + "structure exists on this full subspace type whose real distance is exactly d. "
                    + "It includes symmetry, nonnegativity and the zero diagonal. The final "
                    + "conjunct states separation for every faithful rho, including nonscalar rho. "
                    + "Coincident subspaces and all triples containing zero remain in scope.")),
                Paragraph(Text("For the scalar state, the projection trace theorem gives "
                    + "mu(X)=dim(X)/n. Dimension is monotone and modular. The positive-offset "
                    + "triangle bound directly applies BadicaJaccardArbitraryLattices.result; "
                    + "modularity supplies its log-submodularity hypothesis. Taking the right "
                    + "limit of positive offsets proves the zero-offset bound for each fixed "
                    + "triple. For a zero join the approximating distances are identically zero.")),
                Paragraph(Text("A nonscalar Hermitian operator has unequal eigenvalues M>m>0 "
                    + "on orthonormal vectors e and f. The actual lines spanned by 2e+f and "
                    + "2e-f have zero intersection and join span(e,f). Their common weight is "
                    + "(4M+m)/5 and their join has weight M+m. With the join as the middle "
                    + "subspace their triangle defect is 3(M-m)/(5(c+M+m)), strictly positive "
                    + "for every allowed c. The spectral theorem and trace one then give "
                    + "rho=I/n as the only all-triple case.")),
                Paragraph(Text("For separation, the difference of projections onto two strictly "
                    + "nested subspaces is an orthogonal projection onto a nonzero subspace. "
                    + "Its trace pairing with a faithful state is positive, so mu is strictly "
                    + "monotone. Equality of the meet and join weights therefore forces the "
                    + "two subspaces to coincide. These arguments formalize the tracial "
                    + "classification application in Corollary 4.1 of Born-weighted Jaccard "
                    + "projection geometry. They make no literature originality claim and "
                    + "do not include the separate sharp interval supremum or nonattainment "
                    + "assertions. All statements are general parameterized theorems, rather "
                    + "than finite computations or certified numerical instances."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Statement()
    {
        var n = F.Id("n"); var rho = F.Id("rho"); var c = F.Id("c");
        var x = F.Id("X"); var z = F.Id("Z");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var space = new Formula.Power(complex, n);
        var scalar = Eqn(rho, new Formula.Fraction(F.Id("I"), n));
        var tri = Call("Tri", rho, c);
        var classification = Seq(Par(tri), Sp, Iff, Sp, Par(scalar));
        var separation = All("X", Call("Subspace", space), All("Z", Call("Subspace", space),
            Seq(Par(Eqn(Call("d", rho, c, x, z), D(0))), Sp, Iff, Sp, Par(Eqn(x, z)))));
        var hypotheses = And(Seq(D(2), Sp, Leq, Sp, n), And(Call("PosDef", rho),
            And(Eqn(Call("Tr", rho), D(1)), Seq(D(0), Sp, Leq, Sp, c))));
        return All("n", naturals, All("rho", Call("Matrix", n, n, complex),
            All("c", reals, Imp(hypotheses,
                And(classification, And(Imp(scalar, Call("Metric", rho, c)), separation))))));
    }
}
