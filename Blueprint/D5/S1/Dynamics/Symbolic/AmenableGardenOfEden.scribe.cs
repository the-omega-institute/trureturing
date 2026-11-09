using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class AmenableGardenOfEdenDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/wacker2016gardeneden");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjectivity and finite-disagreement preinjectivity coincide for full cellular maps over every finite alphabet on every discrete group with a nontrivial right counting Følner filter.",
        H("Full cellular maps on groups"), Blocks(
        Paragraph(Text("Let A be a finite alphabet in an arbitrary universe and G a group in an independent universe. "
            + "A finite neighborhood S and a rule φ : (S → A) → A define the full map Φ(x)(g) = φ(s ↦ x(g*s)). "
            + "Configurations are all functions G → A; the group need not be countable, finitely generated or commutative. "
            + "The neighborhood may be empty or asymmetric. Empty and singleton alphabets are included.")),
        Describe.Lean(DescribeId.Create("full-local-map"), DeclarationHandle.Create(Owner + "localMap"),
            H("The full local map"), StatementSource.FromLean(),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("The neighborhood coordinates multiply on the right. Left translation of a configuration therefore commutes with the map."))),
            DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("finite-disagreement-preinjectivity"), DeclarationHandle.Create(Owner + "Preinjective"),
            H("Preinjectivity on finite disagreements"), StatementSource.FromLean(),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("Two configurations with finite disagreement and equal complete images must be equal. "
                    + "Equality of images is equality at every group element."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actual-image-patterns"), DeclarationHandle.Create(Owner + "ImagePatterns"),
            H("Jointly realized image patterns"), StatementSource.FromLean(),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("ImagePatterns(S,φ,F) is the range of x ↦ (f ↦ Φ(x)(f)) on all complete configurations x. "
                    + "One x must realize all coordinates of a pattern simultaneously."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("left-coordinate-replacement"), DeclarationHandle.Create(Owner + "writePattern"),
            H("Replace a pattern on a left translate"), StatementSource.FromLean(),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("On the translate t*C the new value at g is p(t⁻¹*g); outside that translate it is the original value. "
                    + "The coordinate t⁻¹*g is unique and keeps the order of multiplication explicit."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("collision-replacement-count"), DeclarationHandle.Create(Owner + "collision_replacement_count"),
            H("Uniform replacement and actual-image counting from a collision"), StatementSource.FromLean(),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("For distinct configurations x,y with finite disagreement and Φ(x)=Φ(y), there are a finite C and distinct patterns p,q on C. "
                    + "Whenever an ambient z has pattern p on t*C, replacing that pattern by q preserves the complete image Φ(z), for every t and z. "
                    + "This finite statement needs no amenability assumption.")),
                Paragraph(Text("For every finite F there is T contained in F whose translates t*C are pairwise disjoint. "
                    + "Writing a=Nat.card(A), E={1}∪S∪C and U=F*E, the simultaneous bounds are "
                    + "card(F) ≤ card(T)*card(C)², card(T)*card(C) ≤ card(U), and "
                    + "Nat.card(ImagePatterns(S,φ,F)) ≤ (a^card(C)−1)^card(T) * a^(card(U)−card(T)*card(C)).")),
                Paragraph(Text("The collar of the actual disagreement core D is D∪D*S⁻¹*S. Every neighborhood window touching D lies in it. "
                    + "Successive replacements on disjoint left translates preserve one complete image and eliminate p from every selected translate. "
                    + "For each actual image pattern choose one complete source and normalize it in this way. "
                    + "Record the avoiding C-patterns together with the source on the residual part of U. "
                    + "Equal records force equal inputs on every window used to compute the restriction to F, hence equal actual image patterns. "
                    + "This injection gives the count without selecting independent output coordinates."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("amenable-garden-of-eden"), DeclarationHandle.Create(Owner + "garden_of_eden"),
            H("Surjectivity is equivalent to finite-disagreement preinjectivity"), StatementSource.FromLean(),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("Give G the discrete measurable structure. Assume NeBot(maxFoelner(Gᵐᵒᵖ,Measure.count)), "
                    + "where the opposite group acts by (op a) • g = g*a. For every finite S and every rule φ, "
                    + "Function.Surjective(Φ) is equivalent to finite-disagreement preinjectivity. "
                    + "The hypothesis uses the maximal counting Følner filter itself, not a chosen sequence. "
                    + "Finite and trivial groups satisfy this hypothesis; uncountable groups remain in scope. "
                    + "There is no assumption that finite-set volumes diverge.")),
                Paragraph(Text("For every finite E containing 1, finite unions of right translates give "
                    + "1 ≤ card(F*E)/card(F) ≤ 1 + Σ(e∈E) card((F*e)△F)/card(F) whenever F is nonempty. "
                    + "The maximal filter is eventually supported on finite nonempty sets, and each right boundary ratio tends to zero. "
                    + "Thus each fixed finite padding has volume ratio tending to one. "
                    + "The logarithmic packing bound converts avoidance of one C-pattern into a positive deficit independent of F.")),
                Paragraph(Text("Surjectivity realizes every finite output pattern. A finite collision would supply the replacement "
                    + "and joint-count bounds above, contradicting this full count and the padding limit. "
                    + "Conversely, preinjectivity injects arbitrary patterns on F, extended into one constant ambient configuration, "
                    + "into actual image patterns on F*({1}∪S⁻¹). Nonsurjectivity of the continuous map on the compact full product "
                    + "would give a nonempty finite missing output pattern. Left equivariance makes it missing at every left translate. "
                    + "Disjoint placements yield the same positive counting deficit and contradict the preinjective lower count. "
                    + "Product compactness applies to arbitrary G; no enumeration or sequential compactness is used.")),
                Paragraph(Text("Subsingleton alphabets are treated directly before choosing any ambient letter. "
                    + "The result therefore includes empty and singleton alphabets as well as empty neighborhoods. "
                    + "This is the classical amenable-group Moore–Myhill theorem. The multiplicative finite-pattern argument "
                    + "extends the lattice formulation while retaining the same jointly realized meaning of image patterns."))), DescribeRole.Theorem)
        )));
}
