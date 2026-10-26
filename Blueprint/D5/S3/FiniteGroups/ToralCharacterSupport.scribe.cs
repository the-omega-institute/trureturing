using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class ToralCharacterSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exactly C₂ × C₆ supports faithful pointwise projective character matches without a global match in the stated cyclic-product family.",
        H("Complete Support for Toral Character Triples"),
        Blocks(
            Entry("triple", "Triple", "Actual character triples", TripleFormula(),
                "A triple is a function from Fin 3 to the homomorphisms G →* ℂˣ. "
                + "The coordinates are actual complex-unit characters, indexed by 0, 1 and 2. "
                + "Character multiplication below is pointwise multiplication.", DescribeRole.Definition),
            Entry("faithful", "ProjectivelyFaithful", "Trivial projective kernel", FaithfulFormula(),
                "A triple is projectively faithful when the only group element at which all "
                + "three coordinate values coincide is the identity. Equivalently, the kernels "
                + "of the two ratios X₁/X₀ and X₂/X₀ intersect trivially.", DescribeRole.Definition),
            Entry("pointwise", "PointwiseMatched", "A scalar and permutation at each element", PointwiseFormula(),
                "For every element g, a nonzero complex scalar and a permutation match the "
                + "three values. Both choices may depend on g. The definition permits equal "
                + "coordinate values and repeated characters.", DescribeRole.Definition),
            Entry("global", "GloballyMatched", "One character and one permutation", GlobalFormula(),
                "A global match uses one homomorphism G →* ℂˣ and one permutation of Fin 3 "
                + "for all elements. The displayed equalities are equalities of characters.", DescribeRole.Definition),
            Entry("supports", "Supports", "The support predicate", SupportsFormula(),
                "Support requires two projectively faithful triples, pointwise matching, "
                + "and the absence of a global match. No normalization or compatibility "
                + "hypothesis is included in this predicate.", DescribeRole.Definition),
            Entry("source", "Source", "The actual source groups", SourceFormula(),
                "Cyclic n is the existing CyclicPrimePowerAction.Cyclic abbreviation for "
                + "Multiplicative (ZMod n). For positive n this is a cyclic group of order n; "
                + "Cyclic 1 is trivial. Source a b m is their actual direct product. "
                + "The complete support theorem assumes a ≤ b, positive m and odd m.", DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("toral-character-support-classification"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/ToralCharacterSupport.support_iff"),
                H("The complete support classification"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural a, b and m with a ≤ b and positive odd m, "
                        + "Source a b m supports the specified pairs exactly when a=b=1 and m=3. "
                        + "The statement quantifies over all actual character triples through Supports. "
                        + "It includes a=0, trivial factors, m=1, repeated eigenvalues, and every "
                        + "higher power of two.")),
                    Paragraph(Text(
                        "When a=0 the source is cyclic. Match at a generator and choose the "
                        + "twisting character as a quotient of two coordinate characters. Equality "
                        + "at the generator gives equality everywhere, including for the trivial group. "
                        + "For a≥1, the Chinese remainder equivalence ZMod.chineseRemainder gives "
                        + "Source a b m ≃ (Cyclic (2^a) × Cyclic (2^b)) × Cyclic m. "
                        + "Support is transported along this actual group equivalence.")),
                    Paragraph(Text(
                        "Write P=Cyclic (2^a) × Cyclic (2^b) and O=Cyclic m. "
                        + "On P, a matching scalar has order dividing 2^b and its cube is the "
                        + "determinant quotient. Inverting 3 modulo 2^b therefore constructs a "
                        + "single character twist removing these scalars. A faithful triple on "
                        + "a noncyclic finite group has distinct coordinate characters: equality "
                        + "of two coordinates would make a remaining ratio an injective character "
                        + "into a finite cyclic group of roots of unity. The pinned "
                        + "linearIndependent_monoidHom theorem then turns equality of character "
                        + "sums into one permutation aligning the restrictions on P.")),
                    Paragraph(Text(
                        "After this alignment, at every mixed element (p,o) the matching scalar "
                        + "has order dividing 2^b m. Its cube has order dividing m, because the "
                        + "determinant quotient is trivial on P. Coprimality forces its mth power "
                        + "to be one. Taking mth powers in each coordinate equality and using "
                        + "coprimality again proves that the pointwise permutation preserves the "
                        + "three values on P. These conclusions hold for every odd m.")),
                    Paragraph(Text(
                        "If b≥2, P is noncyclic and has an element whose square is nonidentity. "
                        + "Faithfulness implies that one of the coordinate ratios has a value "
                        + "whose square is nonidentity. Three successive translates give three "
                        + "distinct values, so one avoids any two forbidden values. Applying this "
                        + "observation to the two ratios constructs one element p₀ on which the "
                        + "three coordinate values are distinct. At every (p₀,o), preservation of "
                        + "those values forces the permutation to be the identity. The odd-factor "
                        + "coordinate quotients consequently agree, supplying a global twisting "
                        + "character. This excludes all b≥2 for every odd m directly.")),
                    Paragraph(Text(
                        "The remaining noncyclic primary group is C₂². Its faithful ratio map "
                        + "to μ₂ × μ₂ is injective and both groups have four elements, hence "
                        + "it is surjective. This supplies each singleton sign pattern. At an "
                        + "odd cyclic generator, a permitted permutation fixing the singleton "
                        + "is the identity or the complementary transposition. The identity "
                        + "would give a global match. After twisting the first odd coordinate "
                        + "to one, the transpositions for singleton coordinates 0 and 1 force "
                        + "both remaining coordinate values to have cube one. Faithfulness "
                        + "makes the generator's cube the identity, so m divides 3. For m=1 "
                        + "alignment already gives a global match, leaving precisely m=3.")),
                    Paragraph(Text(
                        "For sufficiency use Γ=(μ₂ × μ₂) × μ₃ and the actual characters "
                        + "X(s,t,z)=(1,sz,tz⁻¹) and Y(s,t,z)=(1,sz⁻¹,tz). "
                        + "Their projective kernels are trivial since μ₂∩μ₃={1}. "
                        + "When s=t, interchange coordinates 1 and 2 with scalar one. "
                        + "When (s,t)=(1,−1), interchange coordinates 0 and 1 with scalar z⁻¹; "
                        + "when (s,t)=(−1,1), interchange coordinates 0 and 2 with scalar z. "
                        + "These exhaust the sign patterns. A global twist is trivial on μ₂² "
                        + "by its square and cube constraints; the distinct restricted characters "
                        + "force its permutation to be the identity. The first coordinate then "
                        + "forces the whole twist to be trivial, which would identify z and z⁻¹ "
                        + "for every cube root, contradicting that μ₃ has three elements. "
                        + "Cyclic/root-of-unity equivalences transport this pair to Source 1 1 3."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula,
        string explanation, DescribeRole role) => Describe.Lean(
            DescribeId.Create("toral-character-support-" + id),
            DeclarationHandle.Create("D5/S3/FiniteGroups/ToralCharacterSupport." + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(F.Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Value(Formula x, Formula i, Formula g) =>
        new Formula.Apply(new Formula.Subscript(x, i), [g]);
    private static Formula WithGroup(Formula body) => All("G", Seq(F.Id("Type"), Star),
        Seq(OpenBracket, Call("Group", F.Id("G")), CloseBracket, Sp, body));
    private static Formula OverTriples(Formula body) => WithGroup(
        All("X", Call("Triple", F.Id("G")), All("Y", Call("Triple", F.Id("G")), body)));
    private static Formula TripleFormula() => Disp(WithGroup(Equal(Call("Triple", F.Id("G")),
        new Formula.TypeArrow(Call("Fin", D(3)),
            Call("MonoidHom", F.Id("G"), Call("Units", Seq(Mathbb, Grp(F.Id("C")))))))));

    private static Formula FaithfulFormula()
    {
        var x = F.Id("X"); var g = F.Id("g"); var i = F.Id("i");
        return Disp(WithGroup(All("X", Call("Triple", F.Id("G")),
            Iff(Call("ProjectivelyFaithful", x), All("g", F.Id("G"),
                Implies(All("i", Call("Fin", D(3)), Equal(Value(x, i, g), Value(x, D(0), g))),
                    Equal(g, D(1))))))));
    }

    private static Formula PointwiseFormula()
    {
        var x = F.Id("X"); var y = F.Id("Y"); var g = F.Id("g");
        var l = F.Id("l"); var p = F.Id("p"); var i = F.Id("i");
        var body = All("g", F.Id("G"), Ex("l", Call("Units", Seq(Mathbb, Grp(F.Id("C")))),
            Ex("p", Call("Perm", Call("Fin", D(3))), All("i", Call("Fin", D(3)),
                Equal(Value(y, i, g), Seq(l, Star, Value(x, new Formula.Apply(p, [i]), g)))))));
        return Disp(OverTriples(Iff(Call("PointwiseMatched", x, y), body)));
    }

    private static Formula GlobalFormula()
    {
        var x = F.Id("X"); var y = F.Id("Y"); var e = F.Id("e");
        var p = F.Id("p"); var i = F.Id("i");
        var body = Ex("e", Call("MonoidHom", F.Id("G"), Call("Units", Seq(Mathbb, Grp(F.Id("C"))))),
            Ex("p", Call("Perm", Call("Fin", D(3))), All("i", Call("Fin", D(3)),
                Equal(new Formula.Subscript(y, i),
                    Seq(e, Star, new Formula.Subscript(x, new Formula.Apply(p, [i])))))));
        return Disp(OverTriples(Iff(Call("GloballyMatched", x, y), body)));
    }

    private static Formula SupportsFormula()
    {
        var g = F.Id("G"); var x = F.Id("X"); var y = F.Id("Y");
        var body = Ex("X", Call("Triple", g), Ex("Y", Call("Triple", g),
            And(Call("ProjectivelyFaithful", x), And(Call("ProjectivelyFaithful", y),
                And(Call("PointwiseMatched", x, y), Seq(Neg, Sp, Call("GloballyMatched", x, y)))))));
        return Disp(WithGroup(Iff(Call("Supports", g), body)));
    }

    private static Formula SourceFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var m = F.Id("m");
        var body = Equal(Call("Source", a, b, m), Seq(
            Call("Cyclic", new Formula.Power(D(2), a)), Sp, Times, Sp,
            Call("Cyclic", Seq(new Formula.Power(D(2), b), Star, m))));
        return Disp(All("a", F.Id("Naturals"), All("b", F.Id("Naturals"),
            All("m", F.Id("Naturals"), body))));
    }

    private static Formula ClassificationFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var m = F.Id("m");
        var body = Iff(Call("Supports", Call("Source", a, b, m)),
            And(Equal(a, D(1)), And(Equal(b, D(1)), Equal(m, D(3)))));
        body = Implies(Call("Odd", m), body);
        body = Implies(Seq(D(1), Le, Sp, m), body);
        body = Implies(Seq(a, Le, Sp, b), body);
        return Disp(All("a", F.Id("Naturals"), All("b", F.Id("Naturals"),
            All("m", F.Id("Naturals"), body))));
    }
}
