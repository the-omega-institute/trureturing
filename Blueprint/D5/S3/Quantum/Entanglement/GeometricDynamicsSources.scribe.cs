using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

// A source/provenance guide only. Authored remarks below assert no Lean coverage.
internal sealed class GeometricDynamicsSourcesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primary sources distinguish geometric state transport, conditional gravitational dictionaries, and operational prediction of area sectors.",
        H("Geometric Dynamics: Sources and Scope"),
        Blocks(
            Paragraph(Text("This source guide records literature dependencies and scope distinctions. Its authored formulas are explanatory remarks, not kernel-derived theorem declarations or a claim that a finite quantum code has a gravitational dual.")),
            Describe.Remark(
                DescribeId.Create("state-transport-and-frame-connection"),
                H("Quantum phase space and moving frames"),
                Equal(Id("HBV"), Add(Id("Vh"), Id("iVdot"))),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/ashtekar1997geometrical"),
                    LibraryNoteRef.Create("D5/L/berry2009transitionless")),
                Blocks(Paragraph(Text("Here V is a prescribed moving isometry, HB is the physical generator and h is the logical generator, in units with hbar equal to one. Geometric quantum mechanics and transitionless driving are established inputs. This transport identity does not determine the path of V or a spacetime metric.")))),
            Describe.Remark(
                DescribeId.Create("length-and-twist-conventions"),
                H("Length, twist and fixed boundaries"),
                Equal(Id("omegaWP"), Call("sum", Call("wedge", Id("dell"), Id("dtau")))),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/kawazumi2025wolpert"),
                    LibraryNoteRef.Create("D5/L/do2010asymptoticwp")),
                Blocks(Paragraph(Text("The twist here has the opposite sign to Kawazumi's equation (1). The underlying formula is due to Wolpert. Fixed outer boundary lengths select the relevant symplectic leaf. These moduli-space coordinates are not automatically quantum phases or gravitational canonical momenta.")))),
            Describe.Remark(
                DescribeId.Create("causal-elimination-and-local-cone-term"),
                H("Causal propagation and local curvature entropy"),
                Equal(Id("DeltaS"), Multiply(Id("cR"), Id("Area"))),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/bar2015greenhyperbolic"),
                    LibraryNoteRef.Create("D5/L/vassilevich2003heatkernel"),
                    LibraryNoteRef.Create("D5/L/solodukhin1995conical"),
                    LibraryNoteRef.Create("D5/L/solodukhin1997nonminimal")),
                Blocks(Paragraph(Text("cR denotes only a fixed-prescription local linear-curvature replica coefficient. Retarded Green operators require their own causal function-space hypotheses; Euclidean determinants are not retarded influence functionals. Nonminimal-coupling contact terms prevent an unrestricted identification with ordinary matter von Neumann entropy.")))),
            Describe.Remark(
                DescribeId.Create("area-algebras-and-gravitational-dictionary"),
                H("Area operators and limits of the holographic dictionary"),
                Equal(Id("SA"), Add(Id("aA"), Id("SM"))),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/harlow2017rtqec"),
                    LibraryNoteRef.Create("D5/L/cao2024areaoperators"),
                    LibraryNoteRef.Create("D5/L/cao2026magicgeometries"),
                    LibraryNoteRef.Create("D5/L/faulkner2014gravitation"),
                    LibraryNoteRef.Create("D5/L/lashkari2016canonical")),
                Blocks(Paragraph(Text("SA is boundary entropy, aA is the expectation of a specified central area operator, and SM is the recoverable algebra entropy. General exact subalgebra codes are outside the subsystem-only no-go scope of the 2026 preprint. Continuum first-law and canonical-energy arguments require their established holographic vacuum and region hypotheses. No such continuum identification is inferred from the displayed finite-code decomposition.")))),
            Describe.Remark(
                DescribeId.Create("current-region-prediction-deficiency"),
                H("A separate dynamical prediction task"),
                Equal(Id("delta"), Call("abs", Id("beta"))),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/watrous2009completelybounded"),
                    LibraryNoteRef.Create("D5/L/azouit2016adiabatic"),
                    LibraryNoteRef.Create("D5/L/beny2010approximate")),
                Blocks(Paragraph(Text("In the stated two-sector example, beta is the hidden phase-to-population transfer coefficient and delta is the infimum unhalved diamond error for predicting the future region from its present marginal. The equality and the uniform strong-dephasing estimate are paper derivations, not Lean claims. This task differs from static approximate error correction. Adiabatic elimination is established background; the cited all-orders assertion remains conjectural.")))))));
}
