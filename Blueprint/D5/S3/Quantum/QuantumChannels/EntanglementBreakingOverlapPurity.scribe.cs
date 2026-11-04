using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class EntanglementBreakingOverlapPurityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/EntanglementBreakingOverlapPurity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a fixed rank-one Holevo representation with pure outputs, Kopel's affine overlap equation determines the mean-output purity and forces the nonconstant purity range.",
        H("The overlap-to-purity part of Kopel's equality theorem"),
        Blocks(
            Entry("projector", "projector", "Pure output projectors",
                "For a vector v in complex Euclidean d-space, projector v is the actual complex matrix with entries v_i times the conjugate of v_j. A unit vector gives a positive semidefinite matrix of trace one.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unit-ray-projectors"),
                DeclarationHandle.Create(Prefix + "vecMulVec_eq_of_unit_ray"),
                H("Unit vectors on one ray have the same projector"),
                StatementSource.FromAuthor(UnitRayProjectorsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two unit complex vectors on the same ray have equal outer projectors because their scalar ratio has squared norm one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("projector-trace"),
                DeclarationHandle.Create(Prefix + "projector_trace"),
                H("Unit-vector projectors have trace one"),
                StatementSource.FromAuthor(ProjectorTraceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural dimension and every unit complex Euclidean vector, its outer projector has complex trace one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-projectors"),
                DeclarationHandle.Create(Prefix + "trace_projectors"),
                H("Projector trace products are squared overlaps"),
                StatementSource.FromAuthor(TraceProjectorsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary complex Euclidean vectors v and w, the trace of the product of their outer projectors is the complex coercion of the squared norm of their inner product."))),
                DescribeRole.Theorem),
            Entry("mean-output", "meanOutput", "The mean of the prepared states",
                "For a fixed list of measurement weights alpha and unit output vectors psi, meanOutput is the sum of alpha divided by d times the output projectors. The main theorem proves that this matrix equals the image of I divided by d under the specified Holevo channel.", DescribeRole.Definition),
            Entry("overlap-purity-rigidity", "affine_overlap_purity_and_rigidity", "Equation (7) determines the purity",
                "Fix d at least two, a finite outcome type, strictly positive alpha, unit measurement and output vectors, a complete rank-one POVM, and the actual matrix-linear channel in that fixed Holevo representation. Assume the channel is not constant. If the off-diagonal squared overlaps obey equation (7) of Kopel's supplied v2 additions for an initially arbitrary real number P, then the mean output rho is positive semidefinite of trace one, equals Phi(I/d), every output expectation against rho equals P, and trace(rho squared) equals P. The theorem proves 1/d at most P and P strictly less than one. It also identifies every centered output-projector Hilbert-Schmidt pairing with (1-P) times (d times the corresponding squared measurement overlap minus one) divided by d-1.", DescribeRole.Theorem,
                "The diagonal overlap identities extend the hypothesis from distinct pairs to all pairs. Taking the trace of POVM completeness gives the sum of alpha equal to d, and pairing completeness against each measurement direction gives the weighted measurement overlap sum equal to one. Summing equation (7) therefore forces the output expectations to be P. Averaging those expectations proves the purity identity. Positivity of the Hilbert-Schmidt square of rho-I/d gives the lower bound. If P were one, every centered output projector would have Hilbert-Schmidt norm zero, so all prepared states would equal rho and the fixed channel would be constant, contradicting the hypothesis.",
                "This is the matrix-purity and centered-Gram portion of Theorem 5, under its rank-one and pure-output assumptions. It does not prove that equality in the nuclear norm inequality forces those assumptions, does not establish saturation from equation (7), and does not identify the nuclear and translation terms in the Bloch basis. Those obligations remain for the full equality theorem."))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula UnitRayProjectorsFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula n = F.Id("n"), psi = F.Id("psi"), chi = F.Id("chi"), z = F.Id("z");
        Formula vector = new Formula.TypeArrow(n, complex);
        Formula unit(Formula v) => Seq(Call("dotProduct", Call("star", v), v), Sp, Eq, Sp, D(1));
        Formula outer(Formula v) => Call("vecMulVec", v, Call("star", v));
        return Disp(All("n", F.Id("Type"),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                All("psi", vector, All("chi", vector,
                    Seq(unit(psi), Sp, Rightarrow, Sp, unit(chi), Sp, Rightarrow, Sp,
                        All("z", complex,
                            Seq(psi, Sp, Eq, Sp, z, Sp, Cdot, Sp, chi, Sp, Rightarrow, Sp,
                                outer(psi), Sp, Eq, Sp, outer(chi)))))))));
    }

    private static Formula ProjectorTraceFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula space = Call("EuclideanSpace", complex, Call("Fin", F.Id("d")));
        Formula v = F.Id("v");
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("d"),
                    Seq(Mathbb, Grp(F.Id("N")))),
                new Formula.BoundVariable(FormulaIdentifier.Create("v"), space),
            ],
            Seq(new Formula.Norm(v), Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
                Call("trace", Call("projector", v)), Sp, Eq, Sp, D(1))));
    }

    private static Formula TraceProjectorsFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula space = Call("EuclideanSpace", complex, Call("Fin", F.Id("d")));
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula pairing = Seq(Langle, Sp, v, Comma, Sp, w, Sp, Rangle,
            Underscore, Grp(complex));
        Formula square = Seq(new Formula.Norm(pairing), Caret, Grp(D(2)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("d"),
                    Seq(Mathbb, Grp(F.Id("N")))),
                new Formula.BoundVariable(FormulaIdentifier.Create("v"), space),
                new Formula.BoundVariable(FormulaIdentifier.Create("w"), space),
            ],
            Seq(Call("trace", Seq(Call("projector", v), Sp, Cdot, Sp,
                    Call("projector", w))),
                Sp, Eq, Sp, Call("ofReal", square))));
    }

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role,
        string proof = "", string boundary = "") =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/kopel2026sharpnorm")),
            proof.Length == 0
                ? Blocks(Paragraph(Text(text)))
                : Blocks(Paragraph(Text(text)), Paragraph(Text(proof)), Paragraph(Text(boundary))), role);
}
