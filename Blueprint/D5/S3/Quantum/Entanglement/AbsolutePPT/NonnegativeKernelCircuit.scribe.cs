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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative solution of finitely many homogeneous real equations decomposes into support-minimal solutions, each using at most one more coordinate than equations.",
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
            Paragraph(Text("For a system of three homogeneous inequalities on nonnegative variables, append three nonnegative slack coordinates and use the augmented matrix with a negative identity block. Its nonnegative kernel projects onto the original feasible cone, and each circuit projects to a feasible vector supported on at most four original coordinates. This supplies a general reduction for the three-row spectral relaxation. Identifying the resulting small-support spectral cases and obtaining a final APPT purity bound require further arguments.")))));
}
