using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class SignallingPureProductNegativityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/liuqiudahlstenvedral2025lighttouch");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite-dimensional signalling channel admits a pure product input with strictly positive PDM negativity.",
        H("Pure product inputs detect signalling through PDM negativity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cj-matrix"),
                DeclarationHandle.Create(Module + ".cjMatrix"),
                H("The input-transposed Choi-Jamiolkowski matrix"),
                StatementSource.FromAuthor(Disp(CjFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a complex linear map e between matrix spaces, cjMatrix is the sum of the "
                    + "transposed input matrix units tensored with their images under e. Thus its "
                    + "entry at row (i,r) and column (j,s) is the (r,s) entry of e applied to the "
                    + "matrix unit with row j and column i. This is the transposed-input convention "
                    + "of Eq. eq: CHOI, arxiv.tex lines 161–164 of arXiv:2303.10544v4. "
                    + "The definition applies to arbitrary finite input index types and arbitrary output index types."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pdm-ba"),
                DeclarationHandle.Create(Module + ".pdmBA"),
                H("The reduced two-time pseudo-density matrix"),
                StatementSource.FromAuthor(Disp(PdmFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Form the product of the rank-one operators associated with a and b, and tensor "
                    + "it with the output identity. The two-time pseudo-density matrix is half the "
                    + "sum of its two products with the input-transposed Choi-Jamiolkowski matrix. "
                    + "This is the Jordan product in Theorem thm: 2timesPDM, arxiv.tex lines 166–173 "
                    + "of arXiv:2303.10544v4. Reorder the factors as (A₁,B₂),(B₁,A₂) using the "
                    + "displayed index map, then trace out the first pair. The remaining matrix acts "
                    + "on B₁ together with A₂. The formula is defined for all vectors a and b; "
                    + "unit vectors give a pure product input. The finite dimensions need not be powers of two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-signalling-ba"),
                DeclarationHandle.Create(Module + ".IsSignallingBA"),
                H("Signalling from B to A"),
                StatementSource.FromAuthor(Disp(SignallingFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A channel signals from B to A when its A₂ marginal cannot factor through the "
                    + "A₁ input marginal by any trace-preserving completely positive channel t. "
                    + "The factorization is required on every complex input matrix, including "
                    + "non-Hermitian matrices. This gives the precise marginal-factorization reading "
                    + "of signalling used here. The source discusses semicausal channels at arxiv.tex "
                    + "line 216; its pure product conjecture is at line 231."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A pure product input with strictly positive negativity"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "All four index types are finite and nonempty. Write Q for the channel p "
                        + "followed by tracing out B₂. For a unit vector a, let Eₐ send X to "
                        + "Q applied to the tensor product of the projector onto a with X. "
                        + "Call a map a replacement map if its value at X is the trace of X times "
                        + "one fixed matrix.")),
                    Paragraph(Text(
                        "Tracing out a tensor factor is a quantum channel: its Kraus operators "
                        + "select the coordinates of that factor, and their adjoint products sum "
                        + "to the identity. Appending the maximally mixed state μ on B₁ is also a "
                        + "quantum channel. Its Kraus operators append one coordinate vector each, "
                        + "scaled by the complex image of the real square root of the inverse of "
                        + "the real cardinality of B₁. Their adjoint products again sum to the identity. "
                        + "The matrix μ is the identity scaled by the inverse of the complex image "
                        + "of that cardinality, and has trace one.")),
                    Paragraph(Text(
                        "Unit pure projectors span the complex matrix space. Indeed, the spectral "
                        + "decomposition expresses each Hermitian matrix as a real linear combination "
                        + "of unit eigenvector projectors, with its real eigenvalues embedded in the "
                        + "complex scalars. Every matrix is its Hermitian real part plus the imaginary "
                        + "unit times its Hermitian imaginary part. Thus a complex linear map vanishing "
                        + "on all unit pure projectors vanishes everywhere.")),
                    Paragraph(Text(
                        "Suppose every Eₐ were a replacement map. Compose the channel appending μ, "
                        + "p, and the channel discarding B₂ to obtain a channel t from A₁ to A₂. "
                        + "Evaluating the replacement identity at μ identifies its fixed output matrix "
                        + "with t applied to the projector onto a. The spanning argument then gives "
                        + "Q(Y tensor X) equal to the trace of X times t(Y) for every Y and X. "
                        + "Expanding arbitrary input matrices in product matrix units extends this "
                        + "identity to the required marginal factorization. This contradicts signalling. "
                        + "Consequently some unit a makes Eₐ a non-replacement map.")),
                    Paragraph(Text(
                        "For any a and b, expansion of the Choi-Jamiolkowski entries and the two "
                        + "partial traces reduces the pseudo-density matrix to half of DM + MD, "
                        + "where M is the input-transposed Choi-Jamiolkowski matrix of Eₐ and "
                        + "D is the projector onto b tensored with the identity on A₂. "
                        + "The contraction over A₁ produces exactly Eₐ; the contraction over B₂ "
                        + "is its output partial trace.")),
                    Paragraph(Text(
                        "A non-replacement map E admits orthogonal unit vectors b and c for which "
                        + "E applied to the rank-one operator c b* is nonzero. To see this, suppose "
                        + "all such images vanished. Distinct coordinate vectors first show that "
                        + "every off-diagonal matrix unit has zero image. For distinct indices i and j, "
                        + "use the normalized sum and difference of their coordinate vectors. "
                        + "Their cross image is one half of the difference of the two diagonal "
                        + "matrix-unit images, so those images must agree. Expansion in matrix units "
                        + "then makes E a replacement map, a contradiction. Apply this conclusion "
                        + "to the chosen Eₐ to obtain b and c.")),
                    Paragraph(Text(
                        "Complete positivity makes p preserve Hermitian matrices. Decomposition "
                        + "into Hermitian real and imaginary parts consequently shows that it "
                        + "commutes with taking adjoints. The same holds for Eₐ, so M is Hermitian. "
                        + "Since D is Hermitian, half of DM + MD is Hermitian. Cyclicity of trace "
                        + "and contraction of the Choi-Jamiolkowski matrix identify its trace with "
                        + "the trace of Eₐ applied to the projector onto b. Trace preservation of p "
                        + "and the unit norms of a and b make this trace one.")),
                    Paragraph(Text(
                        "Choose a nonzero (r,s) entry of Eₐ applied to c b*. Let v be c tensored "
                        + "with the s-th coordinate vector of A₂, and w be b tensored with its "
                        + "r-th coordinate vector. Orthogonality and normalization give Dv = 0 "
                        + "and Dw = w. The quadratic form of R = pdmBA(p,a,b) at v is therefore zero. "
                        + "If R were positive semidefinite, zero quadratic form would imply Rv = 0. "
                        + "However, pairing Rv with w gives one half of the chosen nonzero entry: "
                        + "the term containing Dv vanishes, while the other contracts M against b "
                        + "and c. This contradiction proves that R is not positive semidefinite.")),
                    Paragraph(Text(
                        "Finally, the negative part of this Hermitian R is positive semidefinite "
                        + "and nonzero, and hence has strictly positive real trace. The Jordan "
                        + "decomposition expresses R as its positive part minus its negative part, "
                        + "whereas the trace norm is the sum of their real traces. Since the trace "
                        + "of R is one, its trace norm minus one is twice the strictly positive "
                        + "trace of the negative part. Hermiticity identifies R with its adjoint, "
                        + "giving exactly the displayed inequality. In the traceNorm convention "
                        + "the adjoint argument computes the real trace of the square root of RR*, "
                        + "as in Eq. eq: causmono at arxiv.tex lines 143–145. Thus the unit vectors "
                        + "a and b provide the required pure product input."))),
                DescribeRole.Theorem))));

    private static Formula A1 => new Formula.Subscript(Alpha, D(1));
    private static Formula B1 => new Formula.Subscript(Beta, D(1));
    private static Formula A2 => new Formula.Subscript(Alpha, D(2));
    private static Formula B2 => new Formula.Subscript(Beta, D(2));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Type => Seq(F.Id("Type"), Star);
    private static Formula Input => Product(A1, B1);
    private static Formula Output => Product(A2, B2);
    private static Formula Retained => Product(B1, A2);
    private static Formula Discarded => Product(A1, B2);

    private static Formula CjFormula()
    {
        Formula e = F.Id("e"), i = F.Id("i"), j = F.Id("j");
        Formula mapType = Parenthesized(Seq(Matrix(Alpha),
            new Formula.Subscript(To, Seq(F.Id("l"), OpenBracket, Complexes, CloseBracket)),
            Sp, Matrix(Beta)));
        Formula value = SumOver(i, Alpha, SumOver(j, Alpha,
            Kronecker(At(Qualified("Matrix", "single"), j, i, Typed(D(1), Complexes)),
                At(e, At(Qualified("Matrix", "single"), i, j, Typed(D(1), Complexes))))));
        return All(Alpha, Type, All(Beta, Type, Instances(Alpha,
            All(e, mapType, Equal(At(Qualified("cjMatrix"), e), value)))));
    }

    private static Formula PdmFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b"), m = F.Id("m");
        Formula total = Product(Input, Output);
        Formula rho = Kronecker(Kronecker(Projector(a), Projector(b)), Typed(D(1), Matrix(Output)));
        Formula jordan = Smul(Typed(new Formula.Fraction(D(1), D(2)), Complexes),
            Add(Multiply(m, Rho), Multiply(Rho, m)));
        Formula x = F.Id("x");
        Formula indexMap = LambdaOf(x, Product(Discarded, Retained),
            Pair(Pair(First(First(x)), First(Second(x))), Pair(Second(Second(x)), Second(First(x)))));
        Formula value = LetOf(m, Matrix(total), At(Qualified("cjMatrix"), Action(p)),
            LetOf(Rho, Matrix(total), rho,
                At(Qualified("partialTraceLeft"),
                    At(Qualified("Matrix", "submatrix"), jordan, indexMap, indexMap))));
        return FourTypes(All(p, Channel(Input, Output), All(a, Vector(A1), All(b, Vector(B1),
            Equal(At(Qualified("pdmBA"), p, a, b), value)))));
    }

    private static Formula SignallingFormula()
    {
        Formula p = F.Id("p"), t = F.Id("t"), x = F.Id("x");
        Formula factorization = Some(t, Channel(A1, A2), All(x, Matrix(Input),
            Equal(At(Qualified("partialTraceRight"), At(Action(p), x)),
                At(Action(t), At(Qualified("partialTraceRight"), x)))));
        return FourTypes(All(p, Channel(Input, Output),
            Iff(At(Qualified("IsSignallingBA"), p), new Formula.Not(Parenthesized(factorization)))));
    }

    private static Formula ResultFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        Formula r = At(Qualified("pdmBA"), p, a, b);
        Formula positive = new Formula.Relation(Typed(D(0), Reals), FormulaRelationOperator.LessThan,
            Subtract(At(Qualified("traceNorm"), At(Qualified("Matrix", "conjTranspose"), r)), Typed(D(1), Reals)));
        Formula conclusion = Some(a, Vector(A1), Some(b, Vector(B1),
            And(Equal(At(Qualified("dotProduct"), At(Qualified("star"), a), a), Typed(D(1), Complexes)),
                And(Equal(At(Qualified("dotProduct"), At(Qualified("star"), b), b), Typed(D(1), Complexes)), positive))));
        return FourTypes(NonemptyInstances(All(p, Channel(Input, Output),
            Implies(At(Qualified("IsSignallingBA"), p), conclusion))));
    }

    private static Formula FourTypes(Formula body) => All(A1, Type, All(B1, Type,
        All(A2, Type, All(B2, Type, Instances(A1, Instances(B1, Instances(A2, Instances(B2, body))))))));
    private static Formula Instances(Formula type, Formula body) => Seq(Forall, Sp,
        OpenBracket, At(Qualified("Fintype"), type), CloseBracket, Sp,
        OpenBracket, At(Qualified("DecidableEq"), type), CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula NonemptyInstances(Formula body) => Seq(Forall, Sp,
        OpenBracket, At(Qualified("Nonempty"), A1), CloseBracket, Sp,
        OpenBracket, At(Qualified("Nonempty"), B1), CloseBracket, Sp,
        OpenBracket, At(Qualified("Nonempty"), A2), CloseBracket, Sp,
        OpenBracket, At(Qualified("Nonempty"), B2), CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula Matrix(Formula type) => At(Qualified("Matrix"), type, type, Complexes);
    private static Formula Channel(Formula input, Formula output) => At(Qualified("QuantumChannel"), input, output);
    private static Formula Vector(Formula type) => Parenthesized(new Formula.TypeArrow(type, Complexes));
    private static Formula Action(Formula p) => At(Qualified("matrixAction"),
        At(Qualified("QuantumChannel", "toCompletelyPositiveMap"), p));
    private static Formula Projector(Formula a) => At(Qualified("Matrix", "vecMulVec"), a, At(Qualified("star"), a));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula First(Formula x) => Seq(x, Dot, D(1));
    private static Formula Second(Formula x) => Seq(x, Dot, D(2));
    private static Formula Kronecker(Formula a, Formula b) => At(Qualified("Matrix", "kronecker"), a, b);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula LetOf(Formula variable, Formula type, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, Typed(variable, type), Sp, Colon, Eq, Sp, value, Semi, Sp, Parenthesized(body));
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
}
