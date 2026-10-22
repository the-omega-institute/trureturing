using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockFirstDescendantCutsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Signed Half-Current Cuts.",
        H("Finite Signed Half-Current Cuts"),
        Blocks(
            Paragraph(Text("Write J(h,j) for the actual finite colour combination of tensorCurrent, beta for B(h,a), and V(E) for chargedCoefficient. R(E,q) uses J(h,j)V(E+2j+3) when j<q and V(E+2j+3)J(h,j) otherwise. Current mode j+1/2 has cover exponent -2j-3. The physical normal cut is j<0; the ordinary cover-coordinate normalMinusOne split is not substituted.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-cutsummand-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutSummand_finite"),
                H("Finite integer support before summation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every actual tensor vector, the charged field supplies a lower exponent bound and current truncation supplies a uniform upper current bound. Support lies in the finite integer interval from min(q,min(0,L-E-3)) to max(q,cutoff). This includes negative cuts and empty branch intervals, with no occupation restriction. The arbitrary tensor lower bound comes from the already constructed charged field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-cutproduct-step"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_step"),
                H("Exact Ward increment at one cut"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The two finite cut supports admit a common finite union. Finsum subtraction distributes only after both supports are proved finite. All differing summands vanish except j=q; the existing all-integer charged_tensor_current_ward, summed over colours, gives beta times V(E+2)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-cutproduct-telescope"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_telescope"),
                H("Universal signed Ward telescope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Integer induction uses the forward Ward step for nonnegative cuts and solves the same exact step backwards for negative cuts. It proves R(E,q)=R(E,0)+q*beta times V(E+2), including q=0. The pointwise finite sums form a genuine complex-linear endomorphism on ActualTensor; no End-valued infinite support assertion is made."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-leftterm-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.leftTerm_finite"),
                H("Finite creation-side Nat support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The injective substitution j=q-1-k pulls back the proved cut support. Its charged exponent is E+2q+1-2k. This branch is individually finite on every actual tensor state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-rightterm-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.rightTerm_finite"),
                H("Finite annihilation-side Nat support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The injective substitution j=q+k pulls back the proved cut support. Its charged exponent is E+2q+3+2k. This branch is individually finite on every actual tensor state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-cutproduct-nat-reindex"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_nat_reindex"),
                H("Two exact Nat reindexes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The ranges of q-1-k and q+k are respectively the strict lower cut and closed upper cut. Split the original finite-support integer sum into these two indicators and use injective range reindexing. The integer inequalities and toNat inverses are proved for every signed cut."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-cutproduct-zero-normal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_zero_normal"),
                H("Identification with the frozen physical constructor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("At q=0, the two Nat sums are exactly the existing order-zero negativeTerm and positiveTerm. Their individual finite-support proofs justify commuting the finite colour sum and each finsum, so R(E,0) is precisely the existing normalInsertion coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-native-first-descendant-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.native_first_descendant_coefficient"),
                H("Literal Ytw coefficient uses the physical split"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual first-descendant coefficient equals R(E,0) minus beta/2 times V(E+2). The equality consumes the genuine Corr/Ytw coefficient theorem and the proved normal constructor identification; it is not a definition of a descendant field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfirstdescendantcuts-native-first-descendant-mixed-iterate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.native_first_descendant_mixed_iterate"),
                H("Every signed cut gives the mixed product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Add (q+1/2)*beta times V(E+2) to the actual Ytw coefficient of the literal original descendant. The proved signed telescope identifies this with the two individually finite Nat products. This feeds the literal original source-current specialization, rather than assuming twisted Jacobi."))),
                DescribeRole.Theorem),
            Paragraph(Text("All statements use arbitrary LatticeData, IsUnit G.det, finite colour weights, charge, integer exponents and cuts, and ActualTensor vectors. No positivity, rank restriction, charge restriction or module-law premise is added. The Reg mirror attempts the source telescope with exact dependent parameters and typed four-slot obligations; completed source admission is not claimed.")))));
}
