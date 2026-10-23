using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class TierzTracelessFreenessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/tierz2026bpsoddp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The traceless cohomology at p = 5 and N = 4 is not free over the exterior algebra of the diagonal creators.",
        H("Traceless cohomology fails diagonal freeness"), Blocks(
            Paragraph(Text(
                "The matrix size is four and the supercharge has degree five. "
                    + "A Lie subalgebra or submodule used as a type denotes its carrier. "
                    + "Subtype.val denotes the underlying vector of a subtype element. "
                    + "All named objects retain their Lean namespaces.")),
            Node("v", "The traceless one-particle space", "V",
                Equal(Local("V"), At(Qualified("LieAlgebra", "SpecialLinear", "sl"),
                    FinFour(), Complexes())),
                "In v2 §2 the traceless one-particle space consists of trace-zero complex matrices. Here it is Mathlib's LieAlgebra.SpecialLinear.sl (Fin 4) ℂ, the space of trace-zero 4 by 4 complex matrices.",
                AssessedProvenance.FromLiterature(Source)),
            Node("e", "The traceless exterior algebra", "E",
                Equal(Local("E"), At(Qualified("ExteriorAlgebra"), Complexes(), Local("V"))),
                "The traceless Fock space of v2 §2 is the exterior algebra over ℂ of the traceless one-particle space. Its multiplication is exterior multiplication.",
                AssessedProvenance.FromLiterature(Source)),
            Node("creator-vec", "The traceless matrix-unit vectors", "creatorVec", CreatorFormula(),
                "For every pair of indices in Fin 4, creatorVec is the element of V whose underlying matrix is Matrix.single i j 1 minus (if i = j then (1 / 4 : ℂ) else 0) times the identity matrix. The subtraction removes the trace of each diagonal matrix unit, as in v2 §2; off-diagonal matrix units are unchanged.",
                AssessedProvenance.FromLiterature(Source)),
            Node("a", "The matrix of traceless creators", "A",
                All("i", FinFour(), All("j", FinFour(),
                    Equal(LocalCall("A", X("i"), X("j")),
                        At(Qualified("ExteriorAlgebra", "ι"), Complexes(),
                            LocalCall("creatorVec", X("i"), X("j")))))),
                "The matrix A has entries in E. Each entry is ExteriorAlgebra.ι ℂ applied to the corresponding traceless matrix-unit vector. This is the traceless creator matrix A of v2 §2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("q", "The quintic supercharge", "Q",
                Equal(Local("Q"), At(Qualified("Matrix", "trace"),
                    new Formula.Power(Local("A"), D(5)))),
                "Specializing Q_p = Tr(A^p) from v2 §2 to p = 5 gives this element of E. The fifth power is matrix multiplication over the exterior algebra. Q is homogeneous of degree five and Q squared is zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("h", "The traceless diagonal subspace", "H",
                Equal(Local("H"), At(Qualified("Submodule", "span"), Complexes(),
                    At(Qualified("Set", "range"), LambdaOf("i", FinFour(),
                        LocalCall("creatorVec", X("i"), X("i")))))),
                "The diagonal action in v1 §5 and v2 §6.3 comes from the span of all four traceless diagonal vectors. Their sum is zero, and the first three are independent, so H has dimension three.",
                AssessedProvenance.FromLiterature(Source)),
            Node("r", "The exterior algebra of diagonal vectors", "R",
                Equal(Local("R"), At(Qualified("ExteriorAlgebra"), Complexes(), Local("H"))),
                "The anticommuting, square-zero diagonal creators of v1 §5 and v2 §6.3 generate the exterior algebra of H. This is the algebra over which the traceless cohomology is considered.",
                AssessedProvenance.FromLiterature(Source)),
            Node("action-map", "The diagonal inclusion and its action", "actionMap",
                Equal(Local("actionMap"), At(Qualified("ExteriorAlgebra", "map"),
                    At(Qualified("Submodule", "subtype"), Local("H")))),
                "ExteriorAlgebra.map extends the inclusion H into V to a complex algebra map from R to E. The Module R E structure is actionMap.toRingHom.toModule: r acts on x by actionMap r times x. This realizes the diagonal exterior multiplication of v1 §5 and v2 §6.3.",
                AssessedProvenance.FromLiterature(Source)),
            Node("d-r", "The differential as right multiplication", "dR",
                All("x", Local("E"), Equal(LocalCall("dR", X("x")),
                    Mul(X("x"), Local("Q")))),
                "Right multiplication by Q is R-linear because the diagonal action is left multiplication. The source complex in v1 §5 and v2 §6.3 uses left multiplication. Since Q has odd degree, xQ = −CliffordAlgebra.involute (Qx); the grade involution therefore identifies the kernels, and left and right multiplication have the same range. Thus this differential gives the source's cycles and boundaries.",
                AssessedProvenance.FromLiterature(Source)),
            Node("cycles", "The cycles of the traceless complex", "Cycles",
                Equal(Local("Cycles"), At(Qualified("LinearMap", "ker"), Local("dR"))),
                "Cycles is the R-submodule of elements x in E satisfying xQ = 0. It is the cycle space of the traceless complex in v1 §5 and v2 §6.3.",
                AssessedProvenance.FromLiterature(Source)),
            Node("d-to-cycle", "Restricting the differential to cycles", "dToCycle",
                All("x", Local("E"), Equal(
                    At(Qualified("Subtype", "val"), LocalCall("dToCycle", X("x"))),
                    LocalCall("dR", X("x")))),
                "LinearMap.codRestrict gives the R-linear map from E to Cycles whose underlying value at x is dR x. The codomain condition holds because (xQ)Q = x(Q squared) = 0. Its range is the boundary submodule inside Cycles.",
                AssessedProvenance.FromRepo()),
            Node("b-zero", "The traceless cohomology module", "B0",
                Equal(Local("B0"), Seq(Local("Cycles"), Slash,
                    Parenthesized(At(Qualified("LinearMap", "range"), Local("dToCycle"))))),
                "The quotient of Cycles by the range of dToCycle is the traceless cohomology B_0 of v1 §5 and v2 §6.3. Its AddCommGroup B0 and Module R B0 structures are the inherited quotient structures. The R-action is the induced diagonal exterior multiplication.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Freeness over the diagonal exterior algebra", "claim",
                new Formula.Logic(Parenthesized(Local("claim")), FormulaLogicOperator.Iff,
                    Parenthesized(At(Qualified("Module", "Free"), Local("R"), Local("B0")))),
                "At (p,N) = (5,4), this is the freeness conjectured in v1 §5 and proposed as a sufficient explanation in v2 §6.3. Module.Free R B0 asks for freeness as an R-module without imposing a grading. A graded decomposition B_0 as the exterior algebra of H tensored with a graded complex vector space would imply this proposition.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A degree-four obstruction to freeness"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Local("claim")))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text(
                        "Write the fifteen independent entries of A in the order "
                            + "a = A(0,0), b = A(1,1), c = A(2,2), d = A(0,1), "
                            + "e = A(0,2), f = A(0,3), g = A(1,0), h = A(1,2), "
                            + "i = A(1,3), j = A(2,0), k = A(2,1), l = A(2,3), "
                            + "m = A(3,0), n = A(3,1), o = A(3,2). Then A(3,3) = −a−b−c. "
                            + "Let ℓ be the exterior image of creatorVec 0 0 + creatorVec 1 1, so ℓ = a+b. "
                            + "Take the cubic y = −bej + cej + dhj − egk + bhk + chk − bfm − cfm "
                            + "+ dim − elm − fgn + bin − cin − hln + fjo + iko, "
                            + "with each product in the displayed order, and put z = ℓy. "
                            + "Exterior multiplication gives Qz = 0 and ℓz = 0.")),
                    Paragraph(Text(
                        "If B0 were free over R, multiplication by the nonzero diagonal vector ℓ "
                            + "would have kernel equal to image: contraction with a linear functional "
                            + "taking value one on that vector gives this exactness on the exterior algebra "
                            + "of H, and a basis gives it on every free R-module. "
                            + "Apply exactness to the degree-four class of z and lift a preimage to Cycles. "
                            + "Projection to exterior degree three yields a cycle x with ℓx = z, "
                            + "because boundaries have zero degree-four component. "
                            + "Exactness of multiplication by ℓ on E then gives x = y + ℓt for some t.")),
                    Paragraph(Text(
                        "Let π be the exterior algebra map induced by the coordinate projection "
                            + "that kills c, f, h, j, l, n, o and fixes a, b, d, e, g, i, k, m. "
                            + "The products satisfy π(Qℓ) = 0 and π(Qy) = −20·abdegikm. "
                            + "The latter is nonzero because abdegikm is a basis monomial. "
                            + "Hence π(Qx) = π(Qy) + π(Qℓ)π(t) is nonzero, contradicting that x is a cycle. "
                            + "This disproves freeness even without a grading, and therefore also the "
                            + "graded freeness proposed in v1 §5 and v2 §6.3. "
                            + "The separate Hilbert-series divisibility question is not settled by this result."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tierz-2026-traceless-bps-freeness-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula CreatorFormula()
    {
        Formula coefficient = At(Qualified("ite"), Equal(X("i"), X("j")),
            Typed(new Formula.Fraction(D(1), D(4)), Complexes()), Typed(D(0), Complexes()));
        Formula identity = Typed(D(1), At(Qualified("Matrix"), FinFour(), FinFour(), Complexes()));
        Formula matrix = Sub(At(Qualified("Matrix", "single"), X("i"), X("j"),
            Typed(D(1), Complexes())), At(Qualified("HSMul", "hSMul"), coefficient, identity));
        return All("i", FinFour(), All("j", FinFour(),
            Equal(At(Qualified("Subtype", "val"), LocalCall("creatorVec", X("i"), X("j"))), matrix)));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        Formula value = X(parts[0]);
        for (int i = 1; i < parts.Length; i++)
            value = Seq(value, Dot, parts[i] == "ι" ? Iota : X(parts[i]));
        return Seq(Operatorname, Grp(value));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Fermionic", "TierzTracelessFreenessRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinFour() => At(Qualified("Fin"), D(4));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
