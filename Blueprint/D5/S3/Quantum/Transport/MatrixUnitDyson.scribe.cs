using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport;

internal sealed class MatrixUnitDysonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual noncommutative Dyson series constructs the unique solution and transports every moving logical matrix unit on a finite closed interval.",
        H("Constructive transport of moving logical matrix units"),
        Blocks(Describe.Lean(
            DescribeId.Create("constructive-transport"),
            DeclarationHandle.Create("D5/S3/Quantum/Transport/MatrixUnitDyson.constructive_transport"),
            H("Ordered integrals and complete unitary transport"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Analytic/baake2011peanobaker"),
                LibraryNoteRef.Create("D5/L/Dynamics/dyson1949radiation"),
                LibraryNoteRef.Create("D5/L/Quantum/kato1950adiabatic")),
            Blocks(
                Paragraph(Text("For every continuous matrix path K on [0,T] with T nonnegative, the recursive Bochner integral orderedTerm equals the independently defined closed-simplex integral simplexTerm. The simplex product is List.ofFn followed by List.prod in decreasing time order, so no commutation is imposed. Each nonnegative uniform bound M gives the estimate (Mt)^m/m!, including m=0 and T=0.")),
                Paragraph(Text("The series dysonSeries is the actual sum of these recursive terms. It converges absolutely at each point and uniformly on the closed interval, is continuous, solves G(t)=I+integral from 0 to t of K(s)G(s), has within derivative K(t)G(t) at every point including both endpoints, and satisfies G(0)=I. Every continuous solution of that integral equation agrees with G.")),
                Paragraph(Text("For a positive-length interval, finite logical indices d with d nonempty, and finite physical indices n, continuous F and D with the stated entrywise within derivatives and finite-interval matrix-unit multiplication and adjoint laws give the computed generator K=averagedVelocity(F,D)-unitSupport(F) supportVelocity(D). Its skew-adjointness, all matrix-unit and support commutators, the one-logical-index projector formula, and all analytic series clauses are conclusions. G is unitary on both sides, the transported logical matrix units have zero within derivative, and F(t)=G(t)F(0) times the conjugate transpose of G(t). The physical type n may be empty.")),
                Paragraph(Text("The existing constructive_transport proof applies unitary_of_skew_evolution in this same owner to its actual path G=dysonSeries K. For any finite square complex matrix type n, including the empty type, any nonnegative T, and arbitrary K and U, within derivative U'=KU, skew-adjoint K on [0,T], and U(0)=I imply both U(t)^H U(t)=I and U(t) U(t)^H=I on [0,T]. The positive interval uses the original Gram-matrix conservation argument; the singleton uses the initial value. This consumed helper is bind-only proof organization of the existing conservation step and carries no new-mathematics or escape-witness credit.")),
                Paragraph(Text("This owner result concerns the two-sided unitarity of one finite matrix evolution and the original constructive matrix-unit transport. It does not establish a complete controlled recovery application, a generator norm bound, syndrome holonomy for loops, a normalized physical instrument, or finite adaptive protocol laws.")),
                Paragraph(Text("The Peano-Baker and Dyson constructions and projector parallel transport are classical. This declaration assembles their finite-interval realization with the repository's computed full matrix-unit generator; it claims no mathematical priority. The result concerns finite complex matrices and one time interval. It supplies neither a parameter-bundle trivialization nor a physical control-cost or adiabatic-error estimate."))),
            DescribeRole.Theorem))));
}
