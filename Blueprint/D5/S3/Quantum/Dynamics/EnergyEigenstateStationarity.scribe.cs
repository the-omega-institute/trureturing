using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class EnergyEigenstateStationarityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.";
    private static Formula V => F.Id("v");
    private static Formula Rho => F.Id("rho");
    private static Formula U => F.Id("U");
    private static Formula StarOf(Formula x) => Seq(x, Caret, Grp(Star));
    private static Formula Mul(params Formula[] xs) => Seq(xs);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An energy eigenvector acquires only an overall phase under time evolution. "
            + "Its density matrix is constant and its energy variance is zero.",
        H("Energy eigenstates have no changing density record"),
        Blocks(
            Result("exp_mulVec_of_eigenvector", "Exponential action on an eigenvector",
                "Let A be any complex matrix on a finite index type. If Av = mu v, "
                    + "then each power acts by the corresponding power of mu. "
                    + "Continuous linear evaluation on v carries the convergent matrix "
                    + "exponential series to the scalar exponential series. The vector "
                    + "may be zero; neither Hermiticity nor diagonalizability is required.",
                Seq(Equal(Mul(F.Id("A"), V), Mul(F.Id("mu"), V)), Sp, Rightarrow, Sp,
                    Equal(Mul(Call("exp", F.Id("A")), V), Mul(Call("exp", F.Id("mu")), V))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/higham2006eigenstate"))),
            Result("pureDensityState", "The normalized pure density state",
                "For v with conjugate inner product equal to one, its rank-one outer "
                    + "product is positive semidefinite and has trace one. This is the "
                    + "density state used in both the time evolution and the variance.",
                Equal(Rho, Mul(V, StarOf(V))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/higham2006eigenstate")), DescribeRole.Definition),
            Result("energy_eigenstate_stationary", "All real times preserve the density matrix",
                "Assume H is Hermitian, v is normalized, and Hv = Ev with E real. "
                    + "Use units in which hbar equals one and put U = exp(-itH), for any "
                    + "real t. This matrix is unitary. The exponential action theorem "
                    + "gives Uv = exp(-itE)v; multiplying the phase by its conjugate gives "
                    + "one, so U rho U* = rho. Arbitrarily rapid overall phase rotation "
                    + "therefore supplies no changing density record of this isolated state.",
                Seq(Equal(Mul(StarOf(U), U), D(1)), Sp, Land, Sp,
                    Equal(Mul(U, StarOf(U)), D(1)), Sp, Land, Sp,
                    Equal(Mul(U, Rho, StarOf(U)), Rho)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/wikipedia2026stationarystate"))),
            Result("energy_eigenstate_variance_zero", "Zero energy variance",
                "For the same normalized vector satisfying Hv = Ev, the density-state "
                    + "expectations of H and H squared are E and E squared. Thus the "
                    + "variance, defined as the second moment minus the squared mean, "
                    + "vanishes. The scalar time parameter can absorb any nonzero choice "
                    + "of hbar. These statements concern a single energy eigenstate; "
                    + "relative phases between distinct energies are not asserted to be constant.",
                Equal(Call("Var", Rho, F.Id("H")), D(0)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/higham2006eigenstate"))))));

    private static DocumentBlock Result(string name, string title, string prose, Formula formula,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("eigenstationary-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance,
            Blocks(Paragraph(Text(prose))), role);
}
