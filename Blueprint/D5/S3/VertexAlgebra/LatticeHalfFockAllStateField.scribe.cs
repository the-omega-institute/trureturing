using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockAllStateFieldDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite correction is consumed by native Fock-normal fields on the full lattice carrier.",
        H("Corrected Native State Fields"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("half-fock-native-corrected-monomial-enumeration"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_monomial_enumeration"),
                H("The actual assignment consumes the order-independent correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every source monomial and every enumeration of its repeated occurrences, the actual Ytw assignment equals the finite correction-coefficient sum feeding normalPolynomial. The correction permutation theorem is on this live proof path. This does not assert normalWord permutation invariance or full twisted Jacobi."))),
                DescribeRole.Theorem),
            Paragraph(Text("correctedPolynomial applies Corr to the actual ordinary oscillator polynomial, uses Finsupp.lsum to apply normalPolynomial to each supported correction coefficient, and shifts its cover exponent by twice the physical correction shift. Ytw then uses the actual charge Finsupp.lsum on the full original Carrier. Thus neither a replacement charged map nor an assumed twisted-module law is introduced.")),
            Paragraph(Text("Every constituent field is formed only after its statewise coefficient finiteness and lower truncation are proved. The construction uses D : LatticeData and native hu : IsUnit D.G.det, with no PosDef, Leech, rank24, eigenbasis or occupation-cutoff premise. The source monomial basis, finite correction family, actual tensor currents, ActualGround and existing chargedField are retained unchanged.")),
            Describe.Lean(
                DescribeId.Create("half-fock-native-charged-recovery"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_charge"),
                H("Pure charged states recover the existing charged field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual correction of the oscillator unit is supported only at shift zero. The actual normal polynomial selects exactly the existing chargedField. This constructor endpoint introduces no second charged map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-vacuum-recovery"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_vacuum"),
                H("The actual vacuum field is the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The zero-charge state with unit oscillator polynomial maps to the exact identity field, using the existing charged coefficient and its genuine ground representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-neutral-insertion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_current_insertion"),
                H("A neutral single source oscillator is the physical jet insertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The neutral single-occurrence correction is unchanged. Its actual field is normalInsertion into the identity. This equality is consumed by exact native current recovery; it is not an independent novelty claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-current-recovery"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_current"),
                H("The actual source currents recover the existing tensor currents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For source oscillator (i,0), the coefficientwise physical normal-insertion proof identifies Ytw with the existing tensorCurrentField on the original ActualTensor. The sign split is by underlying current mode, not by cover exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-arbitrary-state-lower-truncation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_source_lower_truncation"),
                H("Every arbitrary source state has an actual finite-minimum truncation bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual finite source charge support and correction-shift supports provide a finite set of intermediate native-field orders. Inserting zero makes its minimum defined even for the zero state. Subtracting twice the maximum ordinary source weighted degree gives a lower bound for Ytw on the chosen target vector. The universal Corr shift bound is consumed in the proof. This does not assert a flattened multi-index support estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-enumerated-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_enumerated_expansion"),
                H("The existing corrected assignment consumes arbitrary enumerations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every charge, correction shift and supported monomial, any permutation of its occurrence list gives the same actual Ytw. The existing Corr and shiftLinear are unchanged; normalPolynomial_enumerated_expansion is applied inside the actual constructor. Complex coefficients and repeated occurrences are retained. The correction source weight is k+1, not the target odd weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-full-fock-coefficients"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_fock_normal_coefficients"),
                H("Every corrected coefficient is its unfiltered native Fock-normal sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The finite outer charge, correction-shift and monomial sums contain the genuine all-integer multi-index sum. Its full product is leftAction, the existing chargedCoefficient, then rightAction, with every actual jetScalar and native current retained. The charged exponent is e+2s+2sum(j)+sum(2k+3), precisely the source shift by 2s and jet exponent -2j-2k-3. flatTerm_finite proves pointwise finite support before normalSequence_flattened interchanges the nested sums. This consumes both finite singleton/pair correction and normalWord permutation invariance without an assumed module/Jacobi record or an alternate charged map."))),
                DescribeRole.Theorem),
            Paragraph(Text("Twisted Jacobi, physical all-state translation, sectorTranslation recurrences, ground monodromy and inverse-Gram stress identification remain separate obligations. Ward/locality/original-Q suppliers are not imported into this increment. Reg obligation aliases are not completed four-slot registrations; source admission and Scribe emission are separate from kernel compilation. Full moonshine, CFT, anomaly, fusion, string theory and AdS/CFT remain open.")))));
}
