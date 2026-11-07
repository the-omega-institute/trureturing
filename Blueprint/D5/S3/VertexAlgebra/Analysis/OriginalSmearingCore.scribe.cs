using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Analysis;

internal sealed class OriginalSmearingCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-carrier graph cores and actual closed charge-sector transport for smooth fields.",
        H("Minimal smearing closures and charge sectors"),
        Blocks(
            Paragraph(Text("finiteDomain is the range of the original finite carrier embedding into H_0. finiteDomainEquiv is its injective linear identification with Carrier(D). finiteField(a,f) uses the bounded map smear(a,f,0) on the embedded order(a) representative, so its input domain is finiteDomain and its output lies in H_0. It is proved to be the restriction of field(a,f) on smoothDomain. Its output is not required to remain in the finite carrier.")),
            Paragraph(Text("For x in H_order(a), consider the continuous graph map x->(inclusion(0,order(a))x,smear(a,f,0)x). The algebraic finite-energy truncations converge to x at that Sobolev order, and their graph images belong to the graph of finiteField. Closability and closedness of its closure therefore put the limit in that closed graph. Applying this to each smooth vector proves field<=closure(finiteField). Together with finiteField<=field and monotonicity of closures, this yields equality of the two minimal closures. Mathlib's closureHasCore then proves that finiteDomain is a core for this minimal closed field, without claiming a core for the maximal adjoint.")),
            Paragraph(Text("chargeSector(k,delta) is the topological closure in H_k of embedded original oscillator states with charge delta. The original mode charge law sends delta to a+delta. Continuity extends this transport to the closed Sobolev sectors; summability and closedness pass it through smear(a,f,k). smoothChargeSector(delta) records membership of every component of a compatible smooth family, and smearFamily transports this submodule to smoothChargeSector(a+delta).")),
            Paragraph(Text("To identify this componentwise condition inside H_0, the proof intersects an original charge sector with an original energy grade. Each such intersection is finite dimensional. Its embedded range is closed, and projection of the closed Hilbert charge sector lands in this range. Commutation of grade projections with injective Sobolev inclusions, followed by convergent finite truncations, proves that inclusion into H_0 reflects charge-sector membership. Thus a smooth family lies in smoothChargeSector(delta) exactly when its evaluation lies in chargeSector(0,delta), yielding field_charge_transport on the actual Hilbert domain.")),
            Paragraph(Text("OriginalSmoothFields consumes field_closure_eq, finite_carrier_core and field_charge_transport together with their original definitions. These private components introduce no separate theorem Describe or novelty claim. The original sector, lattice and pairing suppliers retain their attributions; closed graphs, adjoints, finite-dimensional closedness and core machinery reuse Mathlib. Equality of opposite adjoint closures and essential self-adjointness remain outside these results."))),
        []));
}
