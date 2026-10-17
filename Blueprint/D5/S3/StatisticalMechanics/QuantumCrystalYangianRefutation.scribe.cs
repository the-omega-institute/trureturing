using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class QuantumCrystalYangianRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/araujoorlandoreffert2021quantumcrystals");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-box bosonic identity-class state contradicts the proposed expression of the negative-flip potential as a linear combination of affine Yangian generators.",
        H("A three-box obstruction to the quantum-crystal Yangian conjecture"), Blocks(
            Paragraph(Text(
                "Plane partitions are finite lower sets in the coordinatewise order on ℕ³, with coordinates starting at zero. "
                    + "We identify each plane partition with its underlying finite set of boxes. "
                    + "For every plane partition Λ, the ket |Λ⟩ denotes Finsupp.single Λ 1, "
                    + "the state with coefficient one at Λ and zero elsewhere. All coefficients lie in ℂ.")),
            Node("PlanePartition", "Plane partitions as finite lower sets", PlanePartitionFormula(),
                "A finite set of boxes is a plane partition when every box below any of its boxes also belongs to it. "
                    + "The three coordinates carry the product order. These are the crystal configurations "
                    + "on which the box-adding and box-removing operators of Eqs. (2a)–(2b) act."),
            Node("boxCount", "The number of boxes", BoxCountFormula(),
                "The box count is the cardinality of the underlying finite set. "
                    + "It gives the grading preserved by the fermion-boson correspondence of Eq. (46)."),
            Node("removableCount", "The number of removable boxes", RemovableCountFormula(),
                "A box can be removed precisely when it is maximal: every box of the same plane partition "
                    + "above it equals it. Counting these boxes gives the negative flippable plaquettes of Eq. (2b)."),
            Node("State", "Finite complex combinations of plane partitions", StateFormula(),
                "Finsupp denotes finitely supported functions. Thus State is the complex vector space "
                    + "with one basis vector for every plane partition, as in the basis transformation of Eqs. (42)–(46)."),
            Node("IsGrade", "The box-number grading", GradeFormula(),
                "A state has grade n when every plane partition with nonzero coefficient has n boxes. "
                    + "The zero state satisfies this condition for every n. "
                    + "Equation (46) preserves this box-number grading."),
            Node("potentialMinus", "The negative-flip potential", PotentialFormula(),
                "The potential O₋ of Eq. (2b) acts diagonally on the plane-partition basis: "
                    + "for every Λ its value on |Λ⟩ is removableCount(Λ) times |Λ⟩. "
                    + "The displayed complex linear combination map extends these basis values by linearity; "
                    + "the removable count is coerced from ℕ to ℂ."),
            Node("bosonicIdentityThree", "The three-box bosonic identity-class state", BosonicFormula(),
                "The three displayed single-layer plane partitions are the row (3), the hook (2, 1), "
                    + "and the column (1, 1, 1), in that order. Each has three boxes and third coordinate zero. "
                    + "Write v = bosonicIdentityThree. Its coefficients 1, 2, 1 are the S₃ characters "
                    + "on the identity class in (A13), as in Eq. (46) and Appendix C."),
            Node("claim", "The consequence of the Yangian conjecture at v", ClaimFormula(),
                "There are complex linear maps e_j, f_j and φ_j for every natural j, and finitely supported "
                    + "complex coefficient families a, b and c. The vectors e_j v have grade four, the vectors "
                    + "f_j v have grade two, and every φ_j v is a scalar multiple of v. A finite linear "
                    + "combination of these vectors equals O₋ v. These are the consequences at v of Eqs. (49)–(50) "
                    + "and the conjecture in Section VI. No Yangian commutation relations are assumed here, "
                    + "so the conjecture implies this statement."),
            Describe.Lean(
                DescribeId.Create("quantum-crystal-yangian-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The removable-box counts contradict the proposed combination"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The row (3), hook (2, 1) and column (1, 1, 1) have respectively 1, 2 and 1 removable boxes. "
                            + "Consequently O₋ v = |(3)⟩ + 4|(2, 1)⟩ + |(1, 1, 1)⟩. "
                            + "These three shapes are exactly the finite sets displayed in the definition of v.")),
                    Paragraph(Text(
                        "Every proposed vector e_j v or f_j v vanishes at both three-box shapes (3) and (2, 1), "
                            + "by its grade. Every proposed φ_j v is a multiple of v, whose coefficient at (2, 1) "
                            + "is twice its coefficient at (3). Thus every term on the right of the proposed identity, "
                            + "and their finite sum, has at the hook twice its value at the row. "
                            + "The left side O₋ v has coefficient 4 at the hook and coefficient 1 at the row. "
                            + "Since 4 is not twice 1, the identity is impossible. In particular O₋ cannot act on "
                            + "these bosonic states as the asserted linear combination of the generators."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("araujo-orlando-reffert-2020-quantum-crystal-yangian-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("quantum-crystal-yangian-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string first, string second) =>
        Seq(Operatorname, Grp(Seq(V(first), Dot, V(second))));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula QualifiedCall(string first, string second, params Formula[] arguments) =>
        At(Qualified(first, second), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Coordinates() =>
        Seq(Naturals(), Sp, Times, Sp, Parenthesized(Seq(Naturals(), Sp, Times, Sp, Naturals())));
    private static Formula Partitions() => Named("PlanePartition");
    private static Formula States() => Named("State");
    private static Formula Coefficients() => Call("Finsupp", Naturals(), Complexes());
    private static Formula LinearMaps() => Call("LinearMap", Complexes(), States(), States());
    private static Formula Family() => new Formula.TypeArrow(Naturals(), LinearMaps());
    private static Formula Underlying(Formula partition) => QualifiedCall("Subtype", "val", partition);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Scale(Formula scalar, Formula vector) =>
        new Formula.Binary(scalar, FormulaBinaryOperator.Multiply, Parenthesized(vector));
    private static Formula Triple(byte x, byte y, byte z) =>
        Parenthesized(Seq(D(x), Comma, Sp, D(y), Comma, Sp, D(z)));
    private static Formula Ket(Formula partition) => Seq(Bar, partition, Rangle);

    private static Formula PlanePartitionFormula()
    {
        Formula lower = All("p", Coordinates(), All("q", Coordinates(),
            Imp(LE(V("q"), V("p")), Imp(Member(V("p"), V("s")), Member(V("q"), V("s"))))));
        Formula subtype = Seq(OpenBrace, V("s"), Colon, Sp, Call("Finset", Coordinates()),
            Sp, Mid, Sp, lower, CloseBrace);
        return Equal(Partitions(), subtype);
    }

    private static Formula BoxCountFormula() => All("L", Partitions(),
        Equal(Call("boxCount", V("L")), QualifiedCall("Finset", "card", Underlying(V("L")))));

    private static Formula RemovableCountFormula()
    {
        Formula maximal = LambdaOf("p", Coordinates(), All("q", Coordinates(),
            Imp(Member(V("q"), Underlying(V("L"))), Imp(LE(V("p"), V("q")), Equal(V("q"), V("p"))))));
        return All("L", Partitions(), Equal(Call("removableCount", V("L")),
            QualifiedCall("Finset", "card", QualifiedCall("Finset", "filter", maximal, Underlying(V("L"))))));
    }

    private static Formula StateFormula() => Equal(States(), Call("Finsupp", Partitions(), Complexes()));

    private static Formula GradeFormula() => All("n", Naturals(), All("u", States(),
        IffOf(Call("IsGrade", V("n"), V("u")), All("L", Partitions(),
            Imp(Member(V("L"), QualifiedCall("Finsupp", "support", V("u"))),
                Equal(Call("boxCount", V("L")), V("n")))))));

    private static Formula PotentialFormula() => Equal(Typed(Named("potentialMinus"), LinearMaps()),
        QualifiedCall("Finsupp", "linearCombination", Complexes(), LambdaOf("L", Partitions(),
            QualifiedCall("Finsupp", "single", V("L"), Typed(Call("removableCount", V("L")), Complexes())))));

    private static Formula BosonicFormula() => Equal(Named("bosonicIdentityThree"),
        Add(Add(Ket(new Formula.SetLiteral([Triple(0, 0, 0), Triple(1, 0, 0), Triple(2, 0, 0)])),
                Scale(D(2), Ket(new Formula.SetLiteral([Triple(0, 0, 0), Triple(1, 0, 0), Triple(0, 1, 0)])))),
            Ket(new Formula.SetLiteral([Triple(0, 0, 0), Triple(0, 1, 0), Triple(0, 2, 0)]))));

    private static Formula Image(string family) => At(At(V(family), V("j")), Named("bosonicIdentityThree"));
    private static Formula WeightedSum(string coefficients, string family) =>
        QualifiedCall("Finsupp", "sum", V(coefficients), LambdaOf("j", Naturals(),
            LambdaOf("x", Complexes(), Scale(V("x"), Image(family)))));

    private static Formula ClaimFormula()
    {
        Formula conditions = And(All("j", Naturals(), Call("IsGrade", D(4), Image("e"))),
            And(All("j", Naturals(), Call("IsGrade", D(2), Image("f"))),
                And(All("j", Naturals(), Some("t", Complexes(),
                        Equal(Image("phi"), Scale(V("t"), Named("bosonicIdentityThree"))))),
                    Equal(Call("potentialMinus", Named("bosonicIdentityThree")),
                        Add(Add(WeightedSum("a", "e"), WeightedSum("b", "f")), WeightedSum("c", "phi"))))));
        return IffOf(Named("claim"), Some("e", Family(), Some("f", Family(), Some("phi", Family(),
            Some("a", Coefficients(), Some("b", Coefficients(), Some("c", Coefficients(), conditions)))))));
    }
}
