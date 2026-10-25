using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class CayleySubgroupConcentrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rounded displacement packing and proper-stabilizer localization.",
        H("Near invariance forces an exact proper subgroup"),
        Blocks(Describe.Lean(
            DescribeId.Create("near-invariant-localization"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/"
                + "CayleySubgroupConcentration.near_invariant_localization"),
            H("Original-label retention in a proper stabilizer"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/FiniteGroups/bedertbucickravitzmontgomerymuyesser2025cayley")),
            Blocks(
                Paragraph(Text("For every finite possibly nonabelian group K and nonempty "
                    + "set T, let tau=|T|/|K|. A real mean-zero Euclidean unit vector with "
                    + "regular-action correlation at least (1-beta)|T|, where "
                    + "0<=beta<=tau^2/1000, yields an actual proper subgroup L retaining "
                    + "at least (1-50 beta/tau^2)|T| original labels. The retained finset "
                    + "is precisely the elements of L whose original values lie in T.")),
                Paragraph(Text("The action is U_g v(x)=v(xg), with its Euclidean isometry "
                    + "proved by coordinate permutation and its orbit sum zero by finite "
                    + "reindexing. The second moment of D(g)=norm(U_g v-v) is at most "
                    + "2 beta |T|. The closed ball of radius tau/5 contains most labels. "
                    + "Only its positive squared radius is divided out, so beta=0 is included.")),
                Paragraph(Text("Put M=floor(4/tau) and q=(M+2)/3 in the natural numbers. "
                    + "If every successive ball grows, the q shells with indices 3i+1 "
                    + "give disjoint translates of the small ball. Their exact integer "
                    + "cardinalities contradict its density. The resulting plateau at "
                    + "k<=4/tau gives X=B((k-1)tau/5) and the actual left stabilizer "
                    + "L=stabilizer K X. It contains the small ball. Since 1 lies in X "
                    + "and X is contained in B(4/5), the zero orbit sum and triangle "
                    + "inequality force L to be proper.")),
                Paragraph(Text("This is the localization part of the finite-group "
                    + "structural core adapted from Section 4 of the cited paper. "
                    + "Quantitative retained-label descent, the all-real-vector numerical "
                    + "gap, centered-indicator directed cuts, complex eigenvalue readout "
                    + "and full original-colour coset/index consequences remain outside "
                    + "this checkpoint. The intended descent must stop at the numerical "
                    + "condition: eigenvalue real parts alone do not control a nonnormal "
                    + "operator's quadratic forms.")),
                Paragraph(Text("Identity labels and loops are allowed in this structural "
                    + "lemma. This permission does not transfer to rainbow-path consumers. "
                    + "No connector, matching, coupling or absorption proof is certified, "
                    + "and original proper-interval Good and unrestricted AM remain open. "
                    + "The construction is literature-adapted, with no novelty claim.")),
                Paragraph(Text("The faithful dependent-family Reg proof compiles, but its "
                    + "source binding remains declared_unresolved with diagnostic "
                    + "source.residual_requires_open. An accepted binding certificate is "
                    + "missing; no declared_validated audit is claimed. The source-owner "
                    + "disclosure is https://github.com/the-omega-institute/trureturing/issues/21342."))),
            DescribeRole.Theorem))));
}
