using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class CompactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Hilbert-basis approximations and compactness in the operator norm.",
        H("Hilbert-Schmidt and trace-class compactness"), Blocks(
            Item("opNorm_le_sqrt_column_square_sum", "Column bound", NormBound(),
                "A continuous operator with square-summable basis columns equals the synthesized operator on the dense basis span. Thus its actual operator norm is bounded by the square root of the column square sum."),
            Item("finiteColumnApprox", "Finite column approximation", ApproxDef(),
                "P_F is the existing Hilbert-basis Schauder projection onto the finite span of b(F). The approximation is S composed with P_F.", DescribeRole.Definition),
            Item("tailColumnSquareSum", "Complement column square sum", TailDef(),
                "The tail is the real sum over the complement subtype of F, including every zero column.", DescribeRole.Definition),
            Item("finiteColumnApprox_apply_basis", "Projection columns", Columns(),
                "On a selected basis vector the approximation agrees with S, and on every other basis vector it is zero."),
            Item("isCompactOperator_finiteColumnApprox", "Compact approximants", BasisStatement(Call("IsCompactOperator", Approx()), false, true),
                "The projection's actual range equals the span of the finite image b(F), so that range is finite-dimensional and locally compact. Restriction to this range is compact, and continuous postcomposition by the inclusion and S gives the approximation."),
            Item("norm_sub_finiteColumnApprox_le", "Uniform norm tail", BasisStatement(Le(Error(), Call("sqrt", Tail())), true, true),
                "Residual columns vanish on F and equal S(b_i) off F. Their square sum is summable and equals the complement-subtype tail. Applying the column synthesis bound to this residual proves a uniform operator norm estimate on all vectors."),
            Item("norm_sub_finiteColumnApprox_sq_le", "Squared norm tail", BasisStatement(Le(Call("square", Error()), Tail()), true, true),
                "The nonnegative tail permits squaring the norm estimate."),
            Item("tendsto_finiteColumnApprox", "Operator norm convergence", BasisStatement(Call("Tendsto", Call("finiteColumnApprox", B, S), Call("atTop", Call("Finset", W)), Call("nhds", S)), true, false),
                "The directed index is all finite subsets of w, ordered by inclusion. Summable complement tails tend to zero, so the squared residual norms and then their square roots tend to zero. This proves convergence in the normed continuous-linear-map space, without selecting a sequence or using only pointwise convergence."),
            Item("isCompactOperator_of_isHilbertSchmidt", "Hilbert-Schmidt compactness", OperatorStatement(Imp(Call("IsHilbertSchmidt", S), Call("IsCompactOperator", S))),
                "Unpack the arbitrary set-indexed Hilbert basis in the Hilbert-Schmidt premise. Every finite column approximation is compact, and the norm limit is compact because H is complete."),
            Item("isCompactOperator_of_nonneg_isTraceClass", "Positive trace-class compactness", OperatorStatement(Imp(Conj(Call("IsTraceClass", S), Le(D(0), S)), Call("IsCompactOperator", S))),
                "For positive T the actual CFC square root is Hilbert-Schmidt and compact. Its square equals T, and composition with a continuous operator preserves compactness."),
            Item("isCompactOperator_of_isTraceClass", "General trace-class compactness", OperatorStatement(Imp(Call("IsTraceClass", S), Call("IsCompactOperator", S))),
                "The positive absolute value of any trace-class T is trace class and compact. The actual bounded polar factor multiplied by this absolute value equals T, so T is compact. Self-adjointness is unnecessary."),
            Paragraph(Text("All statements retain arbitrary complete complex Hilbert spaces and arbitrary set-indexed Hilbert bases. They require no separability, injectivity, finite ambient dimension or eigenbasis. The trace-class predicate and CFC/polar suppliers are the attributed Physlib analytic infrastructure. These compactness statements supply a premise for later spectral arguments; no complete spectral basis or common energy and heat-trace conclusion follows here.")))));
    private static readonly Formula Hh = F.Id("H"), W = F.Id("w"), B = F.Id("b"), S = F.Id("S"), Ff = F.Id("F"), I = F.Id("i");
    private static Formula Approx() => Call("finiteColumnApprox", B, S, Ff);
    private static Formula Tail() => Call("tailColumnSquareSum", B, S, Ff);
    private static Formula Error() => Call("norm", Call("subtract", S, Approx()));
    private static Formula SqColumn() => Call("square", Call("norm", new Formula.Apply(S, [new Formula.Apply(B, [I])])));
    private static Formula Sum() => Call("tsum", Seq(SqColumn(), I, W));
    private static Formula BasisStatement(Formula body, bool summable, bool finite)
    {
        var xs = new System.Collections.Generic.List<Formula.BoundVariable> {
            new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
            new(FormulaIdentifier.Create("w"), Call("Set", Hh)),
            new(FormulaIdentifier.Create("b"), Call("HilbertBasis", W, Hh)),
            new(FormulaIdentifier.Create("S"), Call("BoundedComplexOperator", Hh)) };
        if (finite) xs.Add(new(FormulaIdentifier.Create("F"), Call("Finset", W)));
        return All([.. xs], summable ? Imp(Call("Summable", Seq(SqColumn(), I, W)), body) : body);
    }
    private static Formula NormBound() => BasisStatement(Le(Call("norm", S), Call("sqrt", Sum())), true, false);
    private static Formula ApproxDef() => BasisStatement(Equal(Approx(), Call("compose", S, Call("basisProjection", B, Ff))), false, true);
    private static Formula TailDef() => BasisStatement(Equal(Tail(), Call("tsum", Seq(SqColumn(), I, Call("complementSubtype", W, Ff)))), false, true);
    private static Formula Columns() => BasisStatement(All([new(FormulaIdentifier.Create("i"), W)],
        Equal(new Formula.Apply(Approx(), [new Formula.Apply(B, [I])]),
            Call("if", Call("member", I, Ff), new Formula.Apply(S, [new Formula.Apply(B, [I])]), D(0)))), false, true);
    private static Formula OperatorStatement(Formula body) => All([
        new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
        new(FormulaIdentifier.Create("S"), Call("BoundedComplexOperator", Hh))], body);
    private static DocumentBlock Item(string name, string title, Formula statement, string explanation, DescribeRole role = DescribeRole.Theorem)
    {
        return Describe.Lean(DescribeId.Create("compact-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/Compact." + name), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")), Blocks(Paragraph(Text(explanation))), role);
    }
    private static Formula Conj(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
