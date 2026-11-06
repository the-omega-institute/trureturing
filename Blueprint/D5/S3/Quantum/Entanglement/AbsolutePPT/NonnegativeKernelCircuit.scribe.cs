using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class NonnegativeKernelCircuitDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.";
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula J => F.Id("J");
    private static Formula M => F.Id("m");
    private static Formula B => F.Id("B");
    private static Formula V => F.Id("v");
    private static Formula W => F.Id("w");
    private static Formula X => F.Id("x");
    private static Formula Vec => Arrow(J, R);
    private static Formula Rows => Call("Fin", M);
    private static Formula Mat => Arrow(Rows, Arrow(J, R));
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(F.Id(n), [.. xs]);
    private static Formula Par(Formula p) => Seq(Open, p, Close);
    private static Formula Arrow(Formula p, Formula q) => Seq(p, To, Sp, q);
    private static Formula And(Formula p, Formula q) => Seq(Par(p), Land, Sp, Par(q));
    private static Formula Imp(Formula p, Formula q) => Seq(Par(p), Rightarrow, Sp, q);
    private static Formula Eq(Formula p, Formula q) => Seq(p, F.Eq, q);
    private static Formula Le(Formula p, Formula q) => Seq(p, Leq, Sp, q);
    private static Formula Ne(Formula p, Formula q) => Seq(p, Neq, Sp, q);
    private static Formula All(string n, Formula t, Formula p) =>
        Seq(Forall, Sp, Par(Seq(F.Id(n), Colon, t)), Comma, Sp, p);
    private static Formula Some(string n, Formula t, Formula p) =>
        Seq(Exists, Sp, Par(Seq(F.Id(n), Colon, t)), Comma, Sp, p);
    private static Formula Set(string n, Formula t, Formula p) =>
        Seq(OpenBrace, Sp, F.Id(n), Colon, t, Mid, Sp, p, CloseBrace);
    private static Formula Supp(Formula v) => Call("nzSupport", v);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Kernel(Formula v) => Call("InKernel", B, v);
    private static Formula Circuit(Formula v) => Call("Circuit", B, v);
    private static Formula Subset(Formula p, Formula q) => Seq(p, Subseteq, Sp, q);
    private static Formula Member(Formula p, Formula q) => Seq(p, InMacro, Sp, q);
    private static Formula Parameters(Formula p, bool matrix = true) =>
        All("J", F.Id("Type"), Seq(OpenBracket, Call("Fintype", J), CloseBracket, Sp,
            matrix ? All("m", N, All("B", Mat, p)) : p));
    private static Formula RowEquation(Formula v) => All("r", Rows,
        Eq(Seq(new Formula.Subscript(F.Sum, Seq(F.Id("j"), Colon, J)), Sp,
            Call("B", F.Id("r"), F.Id("j")), Cdot, Sp, Call("v", F.Id("j"))), D(0)));
    private static Formula Scalar => F.Id("F");
    private static Formula Labels => F.Id("E");
    private static Formula FieldVec => Arrow(Labels, Scalar);
    private static Formula FieldParameters(Formula p, bool ordered) =>
        All("F", F.Id("Type"), ordered
            ? Seq(OpenBracket, Call("Field", Scalar), CloseBracket, Sp,
                OpenBracket, Call("LinearOrder", Scalar), CloseBracket, Sp,
                OpenBracket, Call("IsStrictOrderedRing", Scalar), CloseBracket, Sp,
                All("E", F.Id("Type"), Seq(OpenBracket, Call("Fintype", Labels), CloseBracket, Sp, p)))
            : Seq(OpenBracket, Call("Field", Scalar), CloseBracket, Sp,
                OpenBracket, Call("LinearOrder", Scalar), CloseBracket, Sp,
                All("E", F.Id("Type"), Seq(OpenBracket, Call("Fintype", Labels), CloseBracket, Sp, p))));
    private static Formula KernelEquation(Formula v) => Eq(Call("mulVec", F.Id("A"), v), D(0));
    private static Formula SignClause => All("i", Labels,
        Seq(Par(Eq(Call("c", F.Id("i")), D(0))), Lor, Sp,
            Eq(Call("sign", Call("c", F.Id("i"))), Call("sign", Call("x", F.Id("i"))))));
    private static Formula GlobalMinimality => All("w", FieldVec,
        Imp(And(KernelEquation(W), And(Ne(W, D(0)),
            Subset(Call("supp", W), Call("supp", F.Id("c"))))),
            Eq(Call("supp", W), Call("supp", F.Id("c")))));


    private static Formula FamilyVector => Call("c", F.Id("j"));
    private static Formula FamilyMember => And(Ne(FamilyVector, D(0)),
        And(KernelEquation(FamilyVector), And(
            All("i", Labels, Seq(Par(Eq(Call("c", F.Id("j"), F.Id("i")), D(0))), Lor, Sp,
                Eq(Call("sign", Call("c", F.Id("j"), F.Id("i"))),
                    Call("sign", Call("x", F.Id("i")))))),
            All("w", FieldVec, Imp(And(KernelEquation(W), And(Ne(W, D(0)),
                Subset(Call("supp", W), Call("supp", FamilyVector)))),
                Eq(Call("supp", W), Call("supp", FamilyVector)))))));
    private static Formula Decomposition => FieldParameters(All("m", N,
        All("A", Arrow(Rows, Arrow(Labels, Scalar)), All("x", FieldVec,
        Imp(KernelEquation(X), Some("n", N,
            Some("c", Arrow(Call("Fin", F.Id("n")), FieldVec),
                And(Eq(Seq(new Formula.Subscript(F.Sum, Seq(F.Id("j"), Colon,
                        Call("Fin", F.Id("n")))), Sp, FamilyVector), X),
                    And(Call("LinearIndependent", Scalar, F.Id("c")),
                        And(Le(F.Id("n"), Card(Call("support", X))),
                            And(Le(F.Id("n"), Call("finrank", Scalar,
                                    Call("ker", Call("mulVecLin", F.Id("A"))))),
                                All("j", Call("Fin", F.Id("n")), FamilyMember))))))))))), true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite kernels over any ordered field admit independent sign-conformal decompositions into globally support-minimal circuits, with support and nullity bounds.",
        H("Circuits of a finite nonnegative kernel"), Blocks(
            Describe.Lean(DescribeId.Create("nonnegative-kernel-support"),
                DeclarationHandle.Create(Root + "nzSupport"), H("Nonzero support"),
                StatementSource.FromAuthor(Disp(Parameters(All("v", Vec,
                    Eq(Supp(V), Set("j", J, Ne(Call("v", F.Id("j")), D(0))))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The support consists of the coordinates at which the vector is nonzero. It is a finite set for every finite coordinate type, including the empty type."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonnegative-kernel-equations"),
                DeclarationHandle.Create(Root + "InKernel"), H("Nonnegative homogeneous solutions"),
                StatementSource.FromAuthor(Disp(Parameters(All("v", Vec,
                    Seq(Kernel(V), Iff, Sp, And(All("j", J, Le(D(0), Call("v", F.Id("j")))),
                        RowEquation(V))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The matrix has an arbitrary natural number of rows and an arbitrary finite coordinate type. A feasible vector is coordinatewise nonnegative and has zero scalar product with every row. No rank, nonzero-column or nonempty-type hypothesis is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonnegative-kernel-circuit"),
                DeclarationHandle.Create(Root + "Circuit"), H("Support-minimal solutions"),
                StatementSource.FromAuthor(Disp(Parameters(All("v", Vec,
                    Seq(Circuit(V), Iff, Sp, And(Kernel(V), And(Ne(V, D(0)),
                        All("w", Vec, Imp(And(Kernel(W), And(Ne(W, D(0)),
                            Subset(Supp(W), Supp(V)))), Le(Card(Supp(V)), Card(Supp(W)))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A circuit is a nonzero feasible vector whose support cardinality is minimal among the nonzero feasible vectors with support contained in its support. Scaling is not normalized, so all positive multiples of a circuit are permitted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonnegative-kernel-conic-decomposition"),
                DeclarationHandle.Create(Root + "nonnegKernel_mem_hull_circuit"),
                H("Conic decomposition"),
                StatementSource.FromAuthor(Disp(Parameters(All("x", Vec, Imp(Kernel(X),
                    Member(X, Call("hull", R, Set("v", Vec, Circuit(V))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/muellerregensburger2016elementary")),
                Blocks(Paragraph(Text("Every feasible vector belongs to the pointed conic hull of the circuits. This is the fully nonnegative specialization of the subspace-cone decomposition in Mueller and Regensburger, Theorem 3. Membership has its usual finite meaning: there is a finitely supported family of nonnegative real coefficients on circuits whose weighted sum is exactly the input. Zero is the empty combination. For a nonzero input, choose a feasible vector of minimum support within its support. Subtract the largest permitted positive multiple, determined by the minimum positive coordinate ratio. A coordinate vanishes, the residual stays feasible, and induction on support cardinality finishes the decomposition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonnegative-kernel-deleted-columns"),
                DeclarationHandle.Create(Root + "circuit_deleted_cols_linearIndependent"),
                H("Independent columns after deleting a supported coordinate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Circuit(V), Sp, Rightarrow, Sp,
                    Call("LinearIndependent", Call("supportedColumnsAfterDeleting", B, F.Id("i")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration retains arbitrary finite J with its Fintype instance, arbitrary m, the full matrix B and vector v, the Circuit witness, the supported deleted coordinate i and its support proof. For any supported coordinate of a circuit, the other supported columns are linearly independent. A dependence among them gives a signed kernel direction vanishing at the deleted coordinate. Orient it to have a positive entry and use the existing minimum-ratio subtraction. The deleted coordinate stays positive while another supported coordinate vanishes, contradicting support minimality. This is the classical finite-dimensional elementary-vector argument; it does not assume a cardinality bound. The support bound now follows by the dimension inequality, and the cofactor completeness theorem uses the same independence result to select a nonzero minor."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonnegative-kernel-circuit-cardinality"),
                DeclarationHandle.Create(Root + "circuit_support_card_le"), H("Support bound"),
                StatementSource.FromAuthor(Disp(Parameters(All("v", Vec, Imp(Circuit(V),
                    Le(Card(Supp(V)), Seq(M, Plus, D(1)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A circuit has support cardinality at most the number of rows plus one. Delete one supported coordinate, apply deleted-column independence, and bound the size of that independent family by the dimension of the row-coordinate space. The deleted-column theorem contains the minimum-ratio contradiction once. Every denominator in that argument is positive where used. The statement includes zero rows, dependent rows, zero columns and zero coordinates; with no rows, circuits have at most one supported coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-field-kernel-support"),
                DeclarationHandle.Create(Root + "support"), H("Finite support over a field"),
                StatementSource.FromAuthor(Disp(FieldParameters(All("v", FieldVec,
                    Eq(Call("support", V), Set("i", Labels, Ne(Call("v", F.Id("i")), D(0))))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This finite support records exactly the nonzero coordinates. Its scalar field and finite label type have independent universes. The conic compression proof uses its cardinality."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordered-field-sign-conformal-global-circuit"),
                DeclarationHandle.Create(Root + "signConformalGlobalKernelCircuit"),
                H("A global circuit retaining a prescribed coordinate"),
                StatementSource.FromAuthor(Disp(FieldParameters(All("m", N,
                    All("A", Arrow(Rows, Arrow(Labels, Scalar)), All("x", FieldVec,
                    All("e", Labels, Imp(And(KernelEquation(X), Ne(Call("x", F.Id("e")), D(0))),
                        Some("c", FieldVec, And(KernelEquation(F.Id("c")),
                            And(Ne(Call("c", F.Id("e")), D(0)), And(SignClause, GlobalMinimality))))))))), true))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar field F and finite label type E have independent universes. The only scalar instances are Field F, LinearOrder F and IsStrictOrderedRing F. The matrix has any natural row count m. The notation supp denotes Function.support. Every nonzero signed kernel vector supported in the output has exactly that support: competitors have no sign restriction and need not be nonzero at e. Zero rows, repeated or zero columns and non-Archimedean ordered fields are included.")),
                    Paragraph(Text("Normalize the input orthant by signs ±1. The negative signed e-column is a nonnegative combination of the other original columns. Minimize support among nonnegative representations of this same point p, permitting p = 0 and empty support. An active signed dependence, oriented to have a positive coordinate, permits minimum-ratio subtraction that preserves p and nonnegativity while erasing an active coordinate. The contradiction proves independence of the compressed active columns. Restore coefficient one at e. For every signed supported kernel d, subtract d e times this normalized relation. The residual vanishes at e and on its independent remaining columns, so d is a scalar multiple of the relation. Nonzero d has a nonzero scalar and equal support. Undo the orthant signs. The same-p feasibility and strict erasure is the new reusable inference in this proof; sign transport and finite-sum normalization alone do not supply it. The finite minimum-ratio proof is shared with the original Real API, whose statements and cofactor consumers are preserved. This is the classical elementary-vector method, without a claim of mathematical novelty."))),
                DescribeRole.Theorem),

            Describe.Lean(DescribeId.Create("ordered-field-independent-conformal-circuit-decomposition"),
                DeclarationHandle.Create(Root + "signConformalGlobalKernelCircuitDecomposition"),
                H("An independent conformal circuit decomposition"),
                StatementSource.FromAuthor(Disp(Decomposition)),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/muellerregensburger2016elementary")),
                Blocks(Paragraph(Text("For every kernel vector x there is a finite family c indexed by Fin n whose sum is x. The family is linearly independent over F. Its size is bounded by both the number of nonzero coordinates of x and the dimension over F of the kernel of mulVecLin A. Each summand is nonzero, belongs to the same kernel and is sign-conformal to x. Each is globally support-minimal: every nonzero signed kernel competitor supported within that summand has exactly the same support, without a sign condition on the competitor. Positive scalars have been absorbed into the summands. The scalar and label universes are independent, and the only scalar instances are Field, LinearOrder and IsStrictOrderedRing.")),
                    Paragraph(Text("Apply the prescribed-coordinate circuit theorem to a nonzero residual. The original finite minimum-ratio subtraction, applied to absolute coordinate values, produces a positive multiple of this circuit and a residual in the same orthant with strictly smaller support. The selected boundary coordinate is nonzero in the new summand and zero in the residual. All circuits subsequently extracted from the residual vanish at that coordinate. This one-sided pivot puts the new summand outside their span, so adjoining it preserves independence. Induction terminates with the zero residual. Independence inside the kernel gives the nullity bound. This is the classical elementary-vector conformal-sum result of Mueller and Regensburger, Theorem 3, with the finite ordered-field argument made explicit; no mathematical novelty is asserted. Zero is represented by n = 0. Empty labels, zero rows, arbitrary rank, zero or repeated columns and non-Archimedean ordered fields remain included."))),
                DescribeRole.Theorem),
            Paragraph(Text("A box-fiber optimization application uses the same ordered field F and an arbitrary linear objective L : (E → F) →ₗ[F] F. Fix A, a right-hand side b, lower and upper coordinate bounds l,u and actual feasible vectors x,y satisfying A x = b = A y and l ≤ x,y ≤ u. For minimization assume L y < L x. Decompose the actual displacement d = y - x. Linearity makes the sum of the objective changes L(c j) strictly negative, so at least one summand has negative change. For each coordinate, all summands have the sign of d there and their sum is d. Hence each summand lies between 0 and d in the appropriate order, and x + c j lies on the coordinatewise interval between x and y, inside the same box. It also remains in the same fiber. This produces an improving nonzero global circuit displacement feasible at x, without assuming such a circuit as input. Conversely, any such displacement is an improving feasible point. Thus x is optimal among this box fiber exactly when no feasible nonzero global circuit displacement improves L. This is an existence criterion over a field, not an integer augmentation algorithm, an iteration bound or a claim that the entire family can be added in arbitrary order.")),
            Paragraph(Text("For arbitrary q : E → (Fin d → F), take the homogeneous matrix A with d + 1 rows, first row identically 1 and remaining rows q. The kernel equations are exactly sum x i = 0 and sum x i • q i = 0. Substituting this matrix yields an independent conformal sum of globally minimal affine relations with the same support and kernel-dimension bounds. Both original affine equations hold for every summand, and every signed affine relation supported in a summand has equal support. Original labels are retained even when q has coincident values; d = 0 and empty label types are allowed. The optimization application applies to coefficient boxes in this same affine fiber. No passage to an injective point set, normalized list or separately supplied realization is required.")),
            Paragraph(Text("For arbitrary same-field points q : E → (Fin d → F), an affine relation x with sum x i = 0, sum x i • q i = 0 and x e ≠ 0 gives the application A r i = (1, q i) r with d + 1 homogeneous rows. The output c satisfies both affine equations, retains e, and has its positive labels contained in the positive labels of x and its negative labels contained in the negative labels of x. Every nonzero signed affine competitor supported in c has equal support, including competitors zero at e. The positive coefficient sum is strictly positive, and the negative coefficient sum is its opposite. Delete the zero coefficients, normalize the two sides and use their zero vector sum: both center masses equal one point p. Thus p lies in the convex hull of each strict sign side of c and, by containment, in each corresponding strict sign-side hull of x. The construction keeps the original labels, permits repeated points and d = 0, and uses no Archimedean assumption. This complete universally parameterized application is checked transiently; no separate thin Radon theorem is retained.")),
            Paragraph(Text("For a system of three homogeneous inequalities on nonnegative variables, append three nonnegative slack coordinates and use the augmented matrix with a negative identity block. Its nonnegative kernel projects onto the original feasible cone, and each circuit projects to a feasible vector supported on at most four original coordinates. This supplies a general reduction for the three-row spectral relaxation. Identifying the resulting small-support spectral cases and obtaining a final APPT purity bound require further arguments.")))));
}
