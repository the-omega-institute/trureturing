using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class ActualWordEnumeratedLoopDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive-word loop transport to literal vertex coordinates with both endpoint corrections.",
        H("Actual positive-word loop transport to literal vertex coordinates with both endpoint corrections"),
        Blocks(
            Paragraph(Text("The purpose of rebasing is to connect the actual outOld history chart to the literal vertex coordinates used by the native arithmetic action. The finite kernel ladder and the independent relabel-residue supplier are both consumed; no cochain equality is inserted as a premise.")),
            Paragraph(Text("The loop calculation retains both inverse change-of-basis identities, both coordinate intertwining equations and both time-factor equations. The final period-weight equality follows only after the common endpoint term has been identified and canceled.")),
            Describe.Lean(
                DescribeId.Create("actualwordenumeratedloop-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordEnumeratedLoop.coefficientBasis"),
                H("A literal enumeration gives the actual coefficient basis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an equivalence e : I equivalent to V with I finite and decidable, coefficientBasis e is Pi.basisFun over GyrationDyadic mapped by reindex e. coefficient_apply gives the delta entries at e i, coefficient_repr evaluates at e i, and rows_coefficients computes the actual row entries of any linear map between coefficient spaces. These statements use whole coefficient functions; neither the graph adjacency nor the beam map is replaced by a guessed numerical matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualwordenumeratedloop-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordEnumeratedLoop.chart_change_entries"),
                H("The old chart and new enumeration have literal permutation entries"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any presentation F, natural m and e : Fin m equivalent to F.V, the coefficient change from presentationBasis F to coefficientBasis e has entry one exactly when chart F.vertex i = e j, and zero otherwise. chart_change_inverse supplies both inverse products, even at rank zero. The old basis is the existing outOld history chart and the new basis is the supplied enumeration. Their relationship is derived from coefficient maps, not asserted to identify the chart adjacency with the native signed matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualwordenumeratedloop-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordEnumeratedLoop.word_rebased"),
                H("Connect the actual word cochain to the same endpoint factors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a literal loop w : Word F F, IsUnit(vertex F).time and e : Fin m equivalent to F.V, word_rebased returns a unit a equal to endpointMap w and commuting with the actual time. With b=presentationBasis F, c=coefficientBasis e, C and Cinv in both directions, and s=T.comp(a inverse), it retains both inverse identities, the delta entries of C, and the separate coordinate equations for a and s. It constructs s.comp a=T and a.comp s=T. For every nonzero d divisible by three, it first states localizedCochain(w)+value(b,c,id,T)=value(b,c,id,T)+dyadicGyration of the actual row unit and backward factor, then cancels the identical endpoint term. path_rebased supplies the loop unit, dictionary_forward supplies its actual endpoint map, and ActualRelabelResidue.dictionary_residue supplies the independent weight comparison. The residue supplier is owned by ActualWordRelabelAssembly and belongs to the ActualRelabelResidue namespace."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualwordenumeratedloop-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordEnumeratedLoop.columnUnit"),
                H("Use the actual endomorphism unit in the native column convention"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("columnUnit b a is a genuine unit with value LinearMap.toMatrix b b a and inverse the matrix of the inverse. toMatrix_comp proves both inverse identities in COLUMN order. The preserved original application uses the actual integer-compatible vertex basis and derives native-image equality by scalar extension and the signed stage cut. This construction alone asserts no equality with rho(h)."))),
                DescribeRole.Definition),
            Paragraph(Text("The preserved original application quantifies arbitrary h : ResetFullAut 4. fullAut_has_two_windows gives windows for h and its actual inverse; OriginalPositiveWordAssembly.positive_word supplies a literal Word w and the signed time displacement s, with h(x)=time(s,w.eval(x)) on every original history. word_rebased then returns the actual endpoint unit. The preserved original application separately identifies the coefficient basis and both row factors with the native COLUMN factors, using endpointMap_cast on integer basis vectors and inverse_time_order for their order.")),
            Paragraph(Text("The actual beam action and signed stage cut give rhoD(h)=tau inverse to the power N multiplied by U, with s=-N. Equality of the native image unit transports its inverse too, hence both factors of the arithmetic cochain. time_calibration measures the SAME time unit for every nonzero period divisible by three. CentralizerTimePowers.translated_value supplies its signed contribution; corrected_localized_word supplies the identical history contribution. Their composition is the preserved original application equality between reduced historyGyration of arbitrary h and gamma p hp of originalImage h, for every such p.")),
            Paragraph(Text("Only after this all-period comparison does the preserved original application combine periods three and six, with primitive-orbit counts two and seven. Applying evaluateCentralizer to the shared witnesses of localized_normal_form and retaining its residue clause identifies the same native chi_add: chi_add(h)=2*Multiplicative.toAdd (Gamma (originalImage h))=2*(historyGyration at three plus reduceSix of historyGyration at six). Primitive agreement on literal forward Fix6 gives sufficiency. The preserved conversion to ResetQ4SmallPeriodRefutation.claim gives the lower bound for this same character at every natural n with 0<n<6.")),
            Paragraph(Text("The construction combines existing RS triangles, actual graph and beam dictionaries, and the arithmetic character. It is a repository-derived application with no literature novelty claim.")))));
}
