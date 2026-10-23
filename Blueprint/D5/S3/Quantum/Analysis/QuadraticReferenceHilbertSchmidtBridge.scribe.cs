using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class QuadraticReferenceHilbertSchmidtBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete finite quadratic column moment constructs the original inverse-square-root product and controls the original analytic trace.",
        H("Quadratic Reference Hilbert-Schmidt Bridge"), Blocks(Describe.Lean(
            DescribeId.Create("quadratic-reference-original-operator-hs-bridge"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/QuadraticReferenceHilbertSchmidtBridge.quadratic_reference_hilbertSchmidt_bridge"),
            H("One bounded extension, its full inverse domain, and the trace estimate"),
            StatementSource.FromAuthor(Endpoint()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H be any complete complex Hilbert space, and e any Hilbert basis "
                    + "indexed by a set of H. Let rho and sigma be the original positive trace-class "
                    + "bounded operators. Assume sigma has this eigenbasis with strictly positive real "
                    + "eigenvalues s. No commutation of rho with sigma or with the observable is assumed, "
                    + "and the dimension need not be finite. The quadratic moment Q is the extended "
                    + "nonnegative sum of norm(rho e_i) squared divided by s_i. The finite-Q guard is "
                    + "required before its real value is used.")),
                Paragraph(Text("Define the columns v_i by inverse square root of s_i times rho e_i. "
                    + "The finite moment proves their squared norms summable. For every x, synthesize "
                    + "A x using the common ColumnSynthesis construction, the sum of inner(e_i,x) times v_i. Parseval and the supplied scalar "
                    + "square-sum product estimate prove absolute convergence of this vector series "
                    + "and the bound norm(A x) at most square root of Q times norm(x). The actual "
                    + "series is linear and continuous; orthonormality proves its columns and its "
                    + "exact Hilbert-Schmidt square sum. An extension is constructed, never assumed.")),
                Paragraph(Text("S is the actual bounded positive square root of sigma from continuous "
                    + "functional calculus. Positivity and S squared equals sigma prove S e_i equals "
                    + "square root of s_i times e_i: applying S plus the positive scalar to the residual "
                    + "gives zero, and its nonnegative quadratic form forces the residual to vanish. "
                    + "The columns give A S equals rho. S is injective, and every basis vector is in "
                    + "its range, so the range is dense. invSqrt is the actual partial-map inverse of "
                    + "S on this full range. The inverse law proves A x equals rho invSqrt x for "
                    + "every x in that domain, not just the finite span. S is bounded; its inverse "
                    + "is not assumed bounded.")),
                Paragraph(Text("For any original bounded self-adjoint observable B, put C equals B S. "
                    + "The trace-class square-root supplier and Hilbert-Schmidt ideal make C "
                    + "Hilbert-Schmidt. The norm sum of inner(A e_i,C e_i) converges absolutely. "
                    + "Positive square-root cancellation and self-adjointness of rho identify each "
                    + "term with inner(e_i,rho B e_i), so the actual trace-basis theorem identifies "
                    + "the same sum with Tr(rho B). The second square sum equals the real part of "
                    + "Tr(sigma B squared), by the original eigenbasis and self-adjointness of B. "
                    + "The supplied scalar Cauchy-Schwarz estimate then proves the displayed squared "
                    + "trace bound. No trace cyclicity with an unbounded inverse is used.")),
                Paragraph(Text("The genuine analytic trace, Hilbert-Schmidt ideal, polar factor, "
                    + "basis trace formula and scalar Cauchy-Schwarz are attributed Physlib suppliers "
                    + "at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, "
                    + "Tom Ole Diem, Apache-2.0. The new composition constructs the missing weighted "
                    + "column operator and connects its full actual inverse domain to the original "
                    + "trace. This result alone asserts no continuity of unbounded quantum energy, "
                    + "entropy continuity, all-temperature Hamiltonian, or unrestricted common "
                    + "Hamiltonian conjecture. State trace normalizations are unnecessary."))),
            DescribeRole.Theorem))));
    private static Formula Endpoint()
    {
        Formula h = F.Id("H"), w = F.Id("w"), e = F.Id("e"), rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula s = F.Id("s"), a = F.Id("A"), b = F.Id("B"), i = F.Id("i"), x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R"))), op = Call("BoundedComplexOperator", h);
        Formula ei = new Formula.Apply(e, [i]), si = new Formula.Apply(s, [i]);
        Formula q = Call("tsum", new Formula.Sequence(Call("ofReal", Call("divide",
            Call("square", Call("norm", new Formula.Apply(rho, [ei]))), si)), i, w));
        Formula inv = Call("inverse", Call("FullDomainPartialMap", Call("sqrt", sigma)));
        Formula col = All([new(FormulaIdentifier.Create("i"), w)], Equal(new Formula.Apply(a, [ei]),
            Call("smul", Call("complexOfReal", Call("inverse", Call("sqrt", si))), new Formula.Apply(rho, [ei]))));
        Formula assumptions = And(Call("IsTraceClass", rho), And(Call("IsTraceClass", sigma),
            And(Call("Nonnegative", rho), And(Call("Nonnegative", sigma),
                And(All([new(FormulaIdentifier.Create("i"), w)], Positive(si)),
                    And(All([new(FormulaIdentifier.Create("i"), w)], Equal(new Formula.Apply(sigma, [ei]),
                        Call("smul", Call("complexOfReal", si), ei))),
                        new Formula.Relation(q, FormulaRelationOperator.NotEqual, Call("top"))))))));
        Formula squareSum = Call("tsum", new Formula.Sequence(
            Call("square", Call("norm", new Formula.Apply(a, [ei]))), i, w));
        Formula traceBound = All([new(FormulaIdentifier.Create("B"), op)], Implies(Call("IsSelfAdjoint", b),
            new Formula.Relation(Call("square", Call("norm", Call("rightTrace", rho, b))),
                FormulaRelationOperator.LessThanOrEqual,
                Mul(Call("toReal", q), Call("realPart", Call("rightTrace", sigma, Call("square", b)))))));
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [new(FormulaIdentifier.Create("A"), op)],
            And(Call("IsHilbertSchmidt", a), And(col, And(Equal(squareSum, Call("toReal", q)),
                And(Equal(Mul(a, Call("sqrt", sigma)), rho), And(Call("Dense", Call("domain", inv)),
                    And(All([new(FormulaIdentifier.Create("x"), Call("domain", inv))], Equal(new Formula.Apply(a, [x]),
                        new Formula.Apply(rho, [new Formula.Apply(inv, [x])]))), traceBound)))))));
        return All([new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")), new(FormulaIdentifier.Create("w"), Call("Set", h)),
            new(FormulaIdentifier.Create("e"), Call("HilbertBasis", w, h)), new(FormulaIdentifier.Create("rho"), op), new(FormulaIdentifier.Create("sigma"), op),
            new(FormulaIdentifier.Create("s"), new Formula.TypeArrow(w, real))], Implies(assumptions, conclusion));
    }
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Positive(Formula a) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
