using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class QutritPureLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original pure lifts are unique at unit support across an actual qutrit face.",
        H("Unique pure lifts across a qutrit face"), Blocks(
            Describe.Lean(DescribeId.Create("unique-original-pure-lift"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/QutritPureLift.unique_original_pure_lift"),
                H("Injectivity on the support-one pure slice"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026ssa")), Blocks(
                    Paragraph(Text("Let C be a real pointed cone in a finite-dimensional normed space V, and let u be a real-linear unit strictly positive on the nonzero cone elements. Purity means being an extreme point of the whole u = 1 base. For each pair of distinct original pure states, assume its actual pair face has a whole affine unit-ball chart. Let F be an actual cone face. Its real span is identified by one real-linear equivalence with all complex Hermitian three-by-three matrices. The equivalence carries F onto the positive semidefinite cone and carries the original unit to the real trace. Thus the span has nine real dimensions. Let g be real-linear, nonnegative on C and zero on F. The quotient by this exact span is injective on positive multiples of original pure states with g = 1.")),
                    Paragraph(Text("Equal quotient values put the signed difference of the lifts in the span of F. The signed spectral sum from CartesianVariance.hermitian_spectral_sum pulls back to three distinct original pure points of F with real coefficients, including any zero eigenvalues. When all coefficients have one weak sign, extremality in the original normalized base makes the lifts positively proportional, and their equal support values make the proportionality one.")),
                    Paragraph(Text("For mixed signs, one sign has a single nonzero term. Moving the terms to opposite sides gives a positive sum of an outside pure lift and that spectral atom on one side. Faciality puts an opposite-sign spectral atom in their actual pair ball. The two distinct spectral atoms are zeros of the same nonnegative g. The affine unit-ball formula for a support vanishing at a sphere point forces g to vanish on the whole ball if it also vanishes at a second sphere point. This contradicts the outside lift having support value one.")),
                    Paragraph(Text("This is the unique-lift step of the short carrier-15 quotient proof (XIII160.34), supplied by the independent convex-geometry review. The theorem takes the actual trace-normalized qutrit face as an input. The projected-plane existence and intersection-dimension steps belong to the surrounding paper argument. The carrier-16 and carrier-17 results are outside this theorem's scope."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);

    private static Formula Statement()
    {
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var v = F.Id("V");
        var cone = F.Id("C");
        var face = F.Id("F");
        var u = F.Id("u");
        var g = F.Id("g");
        var e = F.Id("e");
        var x = F.Id("x");
        var r = F.Id("r");
        var p = F.Id("p");
        var a = F.Id("a");
        var span = Call("span", real, face);
        var map = Call("LinearMap", real, v, real);
        Formula Apply(Formula f, Formula y) => new Formula.Apply(f, [y]);

        var unit = All("x", v, Implies(
            And(Rel(x, FormulaRelationOperator.MemberOf, cone), Rel(x, FormulaRelationOperator.NotEqual, D(0))),
            Rel(D(0), FormulaRelationOperator.LessThan, Apply(u, x))));
        var positive = All("x", v, Implies(Rel(x, FormulaRelationOperator.MemberOf, cone),
            Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Apply(g, x))));
        var zeroOnFace = All("x", v, Implies(Rel(x, FormulaRelationOperator.MemberOf, face),
            Rel(Apply(g, x), FormulaRelationOperator.Equal, D(0))));

        var coordinates = All("x", span, new Formula.Logic(
            Rel(Call("val", x), FormulaRelationOperator.MemberOf, face),
            FormulaLogicOperator.Iff, Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Apply(e, x))));
        var trace = All("x", span, Rel(Call("trace", Apply(e, x)), FormulaRelationOperator.Equal,
            Apply(u, Call("val", x))));
        var slice = Call("setOf", Seq(r, Mapsto, Sp,
            Exists("p", Call("pure", cone, u), Exists("a", real,
                And(Rel(D(0), FormulaRelationOperator.LessThan, a),
                    And(Rel(r, FormulaRelationOperator.Equal, Call("smul", a, Call("val", p))),
                        Rel(Apply(g, r), FormulaRelationOperator.Equal, D(1))))))));
        var hypotheses = And(unit, And(positive, And(zeroOnFace,
            And(Call("wholePairBalls", cone, u), And(coordinates, trace)))));
        var hermitian = Call("HermitianMat", Call("Fin", D(3)), complex);
        return All("V", F.Id("Type"), Seq(
            OpenBracket, Call("NormedAddCommGroup", v), CloseBracket, Sp,
            OpenBracket, Call("NormedSpace", real, v), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", real, v), CloseBracket, Sp,
            All("C", Call("PointedCone", real, v),
                All("u", map, All("g", map, All("F", Call("Face", cone),
                    All("e", Call("LinearEquiv", real, span, hermitian),
                        Implies(hypotheses, Call("InjOn", Call("mkQ", span), slice)))))))));
    }
}
