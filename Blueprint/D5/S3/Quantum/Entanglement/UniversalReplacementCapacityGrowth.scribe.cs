using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class UniversalReplacementCapacityGrowthDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal replacement extracts an orthonormal purification family and forces inner capacity growth.",
        H("Universal Replacement Capacity Growth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("universal-replacement"),
                DeclarationHandle.Create(Module + "UniversalReplacement"),
                H("Universal single-step replacement"),
                StatementSource.FromAuthor(ReplacementFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/braunsteinpati2007nohiding")),
                Blocks(Paragraph(Text(
                    "A, B, and R index the previous inner space, next inner space, and emitted "
                    + "space. The product B times R is the finite coordinate realization of "
                    + "their tensor product. DensityState is the existing positive trace-one "
                    + "CStarMatrix subtype. The displayed CStarMatrix.ofMatrix.symm(val(rho)) "
                    + "is exactly CStarMatrix.ofMatrix.symm rho.val, and conjTranspose is the adjoint. "
                    + "This is equation 55.2: the quantifier ranges over every density input, "
                    + "including coherent superpositions, not only the input basis states."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("universal-replacement-capacity-growth"),
                DeclarationHandle.Create(Module + "universal_replacement_capacity_growth"),
                H("Orthonormal extraction and inner capacity"),
                StatementSource.FromAuthor(CapacityFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/braunsteinpati2007nohiding")),
                Blocks(
                    Paragraph(Text(
                        "M and S abbreviate the underlying matrix of tau and its nonzero "
                        + "spectral support. The Lean let hPos transports tau.property.1 through "
                        + "CStarMatrix.ofMatrixStarAlgEquiv.symm and "
                        + "Matrix.nonneg_iff_posSemidef.mp. E and lam are exactly "
                        + "hPos.isHermitian.eigenvectorBasis and eigenvalues. Positivity makes "
                        + "every nonzero eigenvalue positive. No spectral or orthogonality "
                        + "hypothesis is added.")),
                    Paragraph(Text(
                        "In v, fst and snd are the product projections, val removes the support "
                        + "subtype, ofReal casts Real.sqrt into Complex, inv is complex inverse, "
                        + "and smul is complex scalar multiplication. toLp(2, f) is "
                        + "WithLp.toLp 2 f, giving the EuclideanSpace vector. The sum is over "
                        + "all r in R. Thus v is exactly the inverse-square-root normalized "
                        + "contraction of a column of W against the corresponding emitted "
                        + "eigenvector.")),
                    Paragraph(Text(
                        "Universal replacement on normalized pure inputs first determines "
                        + "the diagonal contraction pairing. Complex polarization, including "
                        + "imaginary-phase superpositions, then gives the cross-input Gram "
                        + "identity. Orthonormality is derived from this identity. The final "
                        + "count binds Mathlib's orthonormal linear independence and finite "
                        + "dimension bound; matrix rank is the number of nonzero eigenvalues.")),
                    Paragraph(Text(
                        "The theorem is the exact finite-dimensional no-hiding capacity bound "
                        + "of quantum-reality Theorem 55.2, together with its explicit witness. "
                        + "Equation 55.2 alone is sufficient, so no redundant isometry premise "
                        + "is assumed. This does not assert a result about approximate "
                        + "replacement, small corrections, or arbitrary black-hole models."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Bound(Formula name, Formula type) => Seq(name, Colon, Sp, type);

    private static Formula Product(Formula first, Formula second) =>
        Seq(first, Sp, Times, Sp, second);

    private static Formula ComplexNumbers() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula MatrixValue(Formula state) => new Formula.Apply(Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot, F.Id("ofMatrix"), Dot, F.Id("symm"))), [Call("val", state)]);

    private static Formula TypeBinders() => Seq(
        Forall, Sp, F.Id("A"), Comma, Sp, F.Id("B"), Comma, Sp,
        Bound(F.Id("R"), F.Id("Type")), Comma);

    private static Formula Instances() => Seq(
        Call("Fintype", F.Id("A")), Comma, Sp,
        Call("DecidableEq", F.Id("A")), Comma, Sp,
        Call("Fintype", F.Id("B")), Comma, Sp,
        Call("Fintype", F.Id("R")), Comma, Sp,
        Call("DecidableEq", F.Id("R")), Comma);

    private static Formula DataBinders() => Seq(
        Forall, Sp, Bound(F.Id("W"), Call("Matrix", Product(F.Id("B"), F.Id("R")),
            F.Id("A"), ComplexNumbers())), Comma, Sp,
        Bound(F.Id("tau"), Call("DensityState", F.Id("R"))), Comma);

    private static Formula ReplacementFormula()
    {
        Formula w = F.Id("W");
        Formula rho = F.Id("rho");
        Formula equality = new Formula.Relation(
            Call("partialTraceFirst", Parenthesized(Seq(
                Parenthesized(Seq(w, Sp, Cdot, Sp, MatrixValue(rho))),
                Sp, Cdot, Sp, Call("conjTranspose", w)))),
            FormulaRelationOperator.Equal, MatrixValue(F.Id("tau")));
        Formula allInputs = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), Call("DensityState", F.Id("A")), equality);
        return Disp(new Formula.Aligned([
            TypeBinders(), Instances(), DataBinders(),
            Seq(Call("UniversalReplacement", w, F.Id("tau")), Sp, Colon, Eq, Sp,
                Parenthesized(allInputs), Dot),
        ]));
    }

    private static Formula CapacityFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula r = F.Id("r");
        Formula ia = F.Id("ia");
        Formula supportIndex = Call("val", Call("snd", ia));
        Formula eigenvalue(Formula index) => new Formula.Apply(F.Id("lam"), [index]);
        Formula support = Seq(OpenBrace, Bound(a, F.Id("R")), Sp, Mid, Sp,
            eigenvalue(a), Sp, Neq, Sp, D(0), CloseBrace);
        Formula scalar = Call("inv", Call("ofReal", Call("sqrt", eigenvalue(supportIndex))));
        Formula summand = Seq(Call("star", new Formula.Apply(F.Id("E"), [supportIndex, r])),
            Sp, Cdot, Sp, new Formula.Apply(F.Id("W"),
                [Parenthesized(Seq(b, Comma, Sp, r)), Call("fst", ia)]));
        Formula vector = Call("toLp", D(2), Seq(b, Sp, Mapsto, Sp, new Formula.Subscript(Sum, new Formula.Relation(r, FormulaRelationOperator.MemberOf, F.Id("R"))), Sp, summand));
        Formula orthonormal = Parenthesized(Call("Orthonormal", ComplexNumbers(), F.Id("v")));
        Formula bound = Parenthesized(new Formula.Relation(
            Seq(Call("card", F.Id("A")), Sp, Cdot, Sp, Call("rank", F.Id("M"))),
            FormulaRelationOperator.LessThanOrEqual, Call("card", F.Id("B"))));
        return Disp(new Formula.Aligned([
            TypeBinders(), Instances(), DataBinders(),
            Seq(Call("UniversalReplacement", F.Id("W"), F.Id("tau")), Sp, Implies, Sp),
            Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id("M"), Sp, Colon, Eq, Sp,
                MatrixValue(F.Id("tau")), Comma),
            Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id("E"), Sp, Colon, Eq, Sp,
                Call("eigenvectorBasis", F.Id("M")), Comma, Sp,
                F.Id("lam"), Sp, Colon, Eq, Sp, Call("eigenvalues", F.Id("M")), Comma),
            Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id("S"), Sp, Colon, Eq, Sp,
                support, Comma),
            Seq(Operatorname, Grp(F.Id("let")), Sp,
                Bound(F.Id("v"), Seq(Product(F.Id("A"), F.Id("S")), Sp, To, Sp,
                    Call("EuclideanSpace", ComplexNumbers(), F.Id("B")))), Sp, Colon, Eq, Sp),
            Seq(ia, Sp, Mapsto, Sp, Call("smul", scalar, vector), Comma),
            new Formula.Logic(orthonormal, FormulaLogicOperator.And, bound),
        ]));
    }
}
