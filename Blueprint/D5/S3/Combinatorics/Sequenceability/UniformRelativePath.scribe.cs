using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class UniformRelativePathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal finite-field relative paths from rotational columns and affine row actions.",
        H("Rotational columns, two row orbits, and endpoint insertion"),
        Blocks(
            Paragraph(Text("For every prime p>=5, finite field K of characteristic p and u!=0, "
                + "put N=(p-1)|K|. The result constructs N+2 distinct actual vertices from "
                + "(0,0) to (0,u), whose interior enumerates F_p^* x K once. Their N+1 "
                + "directed full-vector differences enumerate (F_p^* x K) union {(0,u)} once.")),
            Paragraph(Text("For p>=7 the published rotational-column supplier produces d with "
                + "both cyclic inventories and d1=d0+d2. The native chart is "
                + "Phi(j,x)=(d_j,(-1)^j x+b_j), with b2=2u and all other b=0. "
                + "The implementation uses the equivalent signed row variable y=(-1)^j x. "
                + "A full round multiplies by a unit chosen internally from the cyclic group K^*. "
                + "It has precisely the zero-row and nonzero-row orbits. The ordinary and "
                + "closing row-label slopes -2 and -(r+1) are nonzero, proving the full-vector inventory.")),
            Paragraph(Text("The two heads have ambient coordinates (d2,2u),(d1,u). The changed "
                + "arrows restore the removed labels (-d0,2u),(d2,2u) and add (0,u). "
                + "The original cycle-merging lemma joins the two exhaustive orbits and inserts "
                + "the two endpoints into one whole-carrier cycle. Removing its terminal-to-start "
                + "arrow gives the actual path. Characteristic five uses the original published "
                + "complete detour theorem with its unchanged telescope.")),
            Paragraph(Text("The construction follows the supplied native proof and the independently "
                + "audited mathematical chart. Its original column supplier uses the Walecki and "
                + "four-block twizzler constructions of Ollis and Willmott. No novelty or model-diversity "
                + "claim is made. The arbitrary-subset, same-M, Headley induction and odd-product "
                + "parent problems remain open.")),
            Paragraph(Text("The exact-telescope dependent-family Reg proof terms compile, but the "
                + "terminal theorem's binding remains declared_unresolved: IE-C050 ClosedTruthReadout, "
                + "reason unclassified_form, rule source.params. This is the same measured binding "
                + "class disclosed for these five theorems at "
                + "https://github.com/the-omega-institute/trureturing/issues/21090. The audits for "
                + "p_ge_seven_column_setup, pge_whole_carrier_cycle, compose_full_path and "
                + "exists_prime_ge_seven_relative_path remain unfinished. Accepted faithful "
                + "source-parameter/readout reconstruction and binding evidence are missing; "
                + "downstream sourceSelection validity is unestablished. No declared_validated "
                + "certificate is claimed.")),
            Describe.Lean(
            DescribeId.Create("uniform-relative-path-column-setup"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/UniformRelativePath.p_ge_seven_column_setup"),
            H("Original rotational columns and an internal primitive row unit"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The original rotational-column existence theorem supplies both "
                + "cyclic inventories and the three-column relation. Cyclicity of the finite field's "
                + "unit group supplies the row multiplier; characteristic at least seven excludes -1."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("uniform-relative-path-whole-cycle"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/UniformRelativePath.pge_whole_carrier_cycle"),
            H("The actual successor is one cycle on the entire carrier"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The zero and nonzero signed rows are the two exhaustive original "
                + "orbits. The selected-head transposition merges them, then two more transpositions "
                + "insert the endpoint singleton cycles using the original merge_cycles proof."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("uniform-relative-path-composition"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/UniformRelativePath.compose_full_path"),
            H("Enumerating a whole-carrier cycle gives every bounded-sum clause"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The actual orbit Q^n(s) transports both punctured inventories. "
                + "Cycle injectivity and telescoping make every empty-through-full prefix distinct, "
                + "every nonempty bounded interval nonzero, and the total equal to the endpoint displacement."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("uniform-relative-path-prime-ge-seven"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/UniformRelativePath.exists_prime_ge_seven_relative_path"),
            H("The two-cut construction for every prime at least seven"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("All affine labels, both original orbits and all surgery seams "
                + "are discharged internally for arbitrary finite K. No row generator, column word, "
                + "logarithm order, inventory certificate or cycle certificate is a theorem premise."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("uniform-relative-path-all-primes"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/UniformRelativePath.exists_uniform_relative_path"),
            H("The complete universal finite-field relative path"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every prime p>=5, every finite characteristic-p field, and every "
                + "nonzero endpoint displacement are included. The only small-prime branch is the "
                + "published characteristic-five path. No extension-degree or residual-prime exclusion remains."))),
            DescribeRole.Theorem))));
}
