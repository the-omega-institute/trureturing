using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualHigherMassResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual all-layer canonical mass response from integer counting.",
        H("Actual all-layer canonical mass response from integer counting"),
        Blocks(
            Paragraph(Text("SOURCE ONLY: UNCOMPILED_UNACCEPTED. No Lean elaboration, kernel/axiom closure, native report, Scribe compilation, official acceptance, or four-slot Reg validation was run. Full Lean bodies are candidate proof attempts. The ordinary Pro derivation and the independent ordinary audit are fallible inputs, not axioms; this context already includes the repository and prior source candidates. No sterile-context or model-diversity claim is made. Native checking may expose elaboration or proof gaps. Root owns both pre-existing native queues and later integration.")),
            Paragraph(Text("At the two prices eta_minus=(1-s)lambda_X and eta_plus=(1+s)lambda_X, subtract the literal finite canonical coordinate sets. Their layer primes lie exactly in the half-open interval [x_plus,x_minus): a prime at the upper-price root counts; one at the lower-price root does not. Grouping this actual coordinate difference by layer, every integer interval has at most movement+1 points, all counted logarithms are <=log X, the total movement is <=333s sqrt X, and there are at most 6 log X layers. This derives, rather than assumes, the response <=400(s sqrt X log X+log^2 X). The construction includes boundary clamping and simultaneous ties across layers.")),
            Paragraph(Text("Owning Lean source SHA256: 6872df7fcc9b427febddcf30313a0817b6ff786434365190b0eb68bc2756edc5. The complete new-declaration signatures, source line locations, import closure and dependency patches are exposed in source-manifest.json and dependency-boundary.json.")),
            Paragraph(Text("Four-slot Reg is not supplied. Missing evidence after the compiled telescope is an actual full-law variation/realization for this literal prime-power inventory, an exact specialization/control witness on its valid arithmetic domain, the corresponding realization/equivalence proofs, and the residual/open-slot statement accepted by the current Reg contract. Abstract invented spectra, weakened prime support or assumed final inequalities would not be faithful. Root must attach that precise missing-evidence statement to its existing issue workflow after native compilation; no issue or fake declared_validated status is created in this source-only packet.")),
            Describe.Lean(
                DescribeId.Create("actualhighermassresponse-actual-higher-mass-response"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherMassResponse.actual_higher_mass_response"),
                H("actual higher mass response"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem actual_higher_mass_response {X s : ℝ} (hX : exp 2 ≤ X)\n    (hs : 0 < s) (hs2 : s ≤ 1 / 2) :\n    0 ≤ higherMass (strictInteger ((1 - s) * referencePrice X)) -\n      higherMass (strictInteger ((1 + s) * referencePrice X)) ∧\n    higherMass (strictInteger ((1 - s) * referencePrice X)) -\n      higherMass (strictInteger ((1 + s) * referencePrice X)) ≤\n      400 * (s * sqrt X * log X + log X ^ 2)"))),
                DescribeRole.Theorem)
        )));
}
