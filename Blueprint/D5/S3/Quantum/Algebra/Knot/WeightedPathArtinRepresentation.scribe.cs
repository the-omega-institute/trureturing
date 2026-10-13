using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Knot;

internal sealed class WeightedPathArtinRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual weighted path matrices represent a finite Artin presentation and give a function on its algebraic Markov quotient.",
        H("Artin Representation and Signed Markov Descent"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-path-artin-markov-invariant"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/WeightedPathArtinRepresentation.weighted_path_artin_markov_invariant"),
            H("From literal path projections to the algebraic Markov quotient"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let L be any finite decidable type, R any decidable symmetric relation, d strictly positive real vertex weights, and delta a strictly positive real number with the exact Perron equality at every vertex. Let A be a nonzero complex number satisfying delta = -A squared minus A inverse squared. The full endpoint block algebra C(R,n,s) and all empty path fibers are retained. No connectedness, weight symmetry, unit-circle condition or nonempty endpoint-fiber hypothesis is added.")),
                Paragraph(Text("Artin(n) is the actual PresentedGroup on Fin(n-1), with distant commutator relators and adjacent three-letter Artin relators. The zero and one strand presentations have empty generator types. The assignment rho(sigma_i) = A inverse times the identity plus A delta times P_(i+1) is constructed as a MonoidHom from Artin(n) to the units of C(R,n,s). Its explicit inverse is A times the identity plus A inverse delta times the same literal projection. Both adjacent Temperley-Lieb directions are consumed, including WeightedPathReverseTemperleyLieb; inverse and relator identities alone are helper calculations, not separately claimed mathematical breakthroughs.")),
                Paragraph(Text("The strandInclusion is a homomorphism between the actual presented groups, obtained by mapping each old generator to the slot with the same value and checking both relator families. The representation commutes with this inclusion and the actual path-append algebra homomorphism, using the existing projection naturality theorem. The exponent-sum homomorphism into Multiplicative integers descends through all relators. Its additive readout is writhe, with signed integer values.")),
                Paragraph(Text("PositiveBraid is the dependent sum of Artin(n) over natural n with n strictly positive. MarkovStep is defined independently of the trace: conjugation within a layer and each of the positive and negative last-generator stabilizations into the next layer. MarkovEquivalent is its equivalence closure. Define F(n,beta) = delta to the n-minus-one times (-A cubed) to the integer writhe of beta times tau(n,s)(rho(beta)). The theorem proves F agrees on every finite Markov equivalence chain. markovValue is an actual Quotient.lift to the algebraic Markov quotient, using that theorem.")),
                Paragraph(Text("For this crossing convention, the normalized tau stabilization coefficients are -A inverse cubed divided by delta for the positive generator, and -A cubed divided by delta for the negative generator. The positive move increments writhe by one and the negative move decrements it by one. In both cases the delta factor and integer writhe factor cancel the trace coefficient. The positive strand restriction is explicit; natural-number subtraction is not used to hide a zero-level normalization exception.")),
                Paragraph(Text("This is classical Jones and Temperley-Lieb mathematics. Aharonov, Jones and Landau, arXiv:quant-ph/0511096v2, Definition 2.5 and equation (4), use the crossing formula A E_i plus A inverse identity. The present E_i is delta times the literal projection. Their line-graph construction is not cited as an arbitrary-graph source theorem; the present actual binding reuses the repository's arbitrary finite Perron path results. Jones, A polynomial invariant for knots via von Neumann algebras, Bulletin of the AMS 12 (1985), pages 104-105, supplies the original trace and writhe construction. The reciprocal crossing convention A identity plus A inverse E_i would require the opposite writhe correction and is not mixed into this statement.")),
                Paragraph(Text("AlgebraicMarkovClass has not been identified with ambient-isotopy classes of oriented tame links. A geometric closure map, Alexander surjectivity, both directions of the geometric Markov theorem and a convention-preserving Jones identification are still required for that interpretation. This complex path-model result gives no Laurent integrality, finite-field specialization, prescribed polynomial realization or solution of Aiello-Baader-Ferretti Question 1 at p=3. Arbitrary positive Perron data also do not imply unitarity of this representation."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula EqTo(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Statement()
    {
        Formula r = F.Id("R"), d = F.Id("d"), delta = F.Id("delta"), a = F.Id("A");
        Formula s = F.Id("s"), b = F.Id("beta"), c = F.Id("gamma");
        Formula value(Formula x) => Call("F", r, d, delta, a, s, x);
        Formula equality = EqTo(value(b), value(c));
        Formula invariant = All("s", F.Id("L"),
            All("beta", Call("PositiveBraid"), All("gamma", Call("PositiveBraid"),
                Seq(Call("MarkovEquivalent", b, c), Rightarrow, Sp, equality))));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Call("FiniteDecidable", F.Id("L")), Semi, Sp,
            Call("SymmetricPositivePerronData", r, d, delta), RowBreak,
            Call("Nonzero", a), Semi, Sp,
            EqTo(delta, Seq(Minus, Call("Pow", a, D(2)), Minus,
                Call("Pow", Call("Inv", a), D(2)))), RowBreak,
            invariant, End, Grp(F.Id("gathered"))));
    }
}
