using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class DelgadoSuerYesilPhiRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/delgadosueryesil2026symmetrization");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pseudo-Frobenius row deletion omits 1 for every proper numerical semigroup, excluding a symmetric numerical set containing 1.",
        H("An obstruction to unrestricted symmetrization surjectivity"), Blocks(
            Paragraph(Text("The final paragraph of Section 5 asks: ‘A natural question is whether Φ is surjective, that is, whether every symmetric numerical set arises as the symmetrization of some almost symmetric numerical semigroup.’ The terminal theorem refutes this unrestricted assertion. Characterizing the whole image remains a separate problem.")),
            Paragraph(Text("Delgado, Suer and Yesil associate a boundary to a proper numerical set by scanning the natural numbers from zero to its largest gap: membership gives a right step and a gap gives an up step. The gap label of a row is its first-column hook length. Their Theorem 4.2 deletes exactly the original pseudo-Frobenius rows other than the Frobenius row. The inverse correspondence reads the resulting boundary; deleted up steps shift later labels without changing retained row lengths.")),
            Describe.Lean(DescribeId.Create("delgado-phi-carrier"), DeclarationHandle.Create(Prefix + "NumericalSet"),
                H("All proper numerical sets"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("NumericalSet stores an arbitrary nonempty finite set of natural-number gaps with zero excluded. Its complement is therefore cofinite, contains zero and is proper. Conversely every proper numerical set has exactly such a finite gap set. The carrier imposes no additive closure and no bound on Frobenius number, genus, type, multiplicity or size."))), DescribeRole.Definition),
            Entry("members", "Membership", membersFormula(),
                "The members are exactly the naturals outside the complete finite gap set.", DescribeRole.Definition),
            Entry("frobenius", "The largest gap", frobeniusFormula(),
                "frobenius U is the maximum of the nonempty finite gap set, as a natural number. Lean uses max' with the nonemptiness proof; the improper numerical set is excluded by the carrier.", DescribeRole.Definition),
            Entry("Semigroup", "Unbounded additive closure", SemigroupFormula(),
                "Both summands range over all natural numbers. The numerical set is a semigroup precisely when its members are closed under addition.", DescribeRole.Definition),
            Entry("PseudoFrobenius", "The original pseudo-Frobenius predicate", PseudoFrobeniusFormula(),
                "A pseudo-Frobenius number is an original gap whose sum with every positive source member belongs to the source. This predicate is evaluated before any row is deleted.", DescribeRole.Definition),
            Entry("AlmostSymmetric", "Almost symmetry", AlmostSymmetricFormula(),
                "The genus is the cardinality of all gaps; the type is the cardinality of the pseudo-Frobenius gaps. AlmostSymmetric includes additive closure and the equality 2g = F + t.", DescribeRole.Definition),
            Entry("Symmetric", "Symmetry without additive closure", SymmetricFormula(),
                "Every natural a from zero through F is considered. Exactly one of a and F-a belongs. Subtraction agrees with integer subtraction on this interval. No semigroup condition is imposed on the target.", DescribeRole.Definition),
            Entry("rowLength", "Horizontal coordinates of the full boundary", rowLengthFormula(),
                "For an original gap r, its row length is the number of right steps preceding its up step. The complete boundary has one row for each original gap, ordered by that gap. Counting preceding right and up steps gives rowLength(U,r) plus the number of gaps below r equal to r.", DescribeRole.Definition),
            Entry("retainedRows", "Precisely the retained original rows", retainedRowsFormula(),
                "Retain an original gap row exactly when its label is F or is not pseudo-Frobenius. Thus exactly PF(U) minus {F(U)} is deleted. The Frobenius row remains, and pseudo-Frobenius status is never recomputed after deletion.", DescribeRole.Definition),
            Entry("inverseBoundary", "Inverting the row boundary", inverseBoundaryFormula(),
                "For each row r in increasing original-label order, the inverse gap label is its horizontal coordinate l(r) plus the number of preceding retained up steps. On a retained subfamily of the original diagram, row lengths remain positive and nondecreasing; the inverse labels are strictly increasing. This is the inverse boundary correspondence, including all multiplicities of equal row lengths.", DescribeRole.Definition, false),
            Entry("deleteRows", "The label shift caused by deletion", deleteRowsFormula(),
                "When R is a subset of the original gap set, each retained label decreases by the number of deleted gaps strictly before it. The proof establishes that this equals inverseBoundary(R,rowLength(U)): partition the original gaps below r into retained and deleted gaps, and use the complete boundary count. The equivalence is used in the exclusion of 1.", DescribeRole.Definition),
            Entry("phi", "The original row-deletion map", phiFormula(),
                "phi U is the complement of the shifted retained gaps. All other natural numbers belong, including the cofinite tail. Restricted to almost symmetric semigroups this is the map in Theorem 4.2, defined by the original row deletion. The argument below does not assume the paper's output-symmetry theorem or execute the extracted GAP pseudocode.", DescribeRole.Definition),
            Entry("phi_omits_one", "A surviving length-one row", phiomitsoneFormula(),
                "Let F be the largest gap. If there is no positive source member at most F, the retained F row has length one. Otherwise let M be the greatest such member and put r=F-M. Since M<F, r is positive. Additive closure would put F in the source if r were a member, so r is a gap. The positive member M witnesses that r is not pseudo-Frobenius, because r+M=F is a gap. Any positive source member a<r would put M+a in the source strictly between M and F, contrary to maximality. Therefore this retained r row has length one. The first retained row is no longer, and its length is positive since zero belongs to the source. Its inverse label is consequently one. This holds for every proper numerical semigroup, independently of almost symmetry and with no size bound.", DescribeRole.Theorem, false),
            Entry("claim", "The whole unrestricted event", claimFormula(),
                "For every proper symmetric numerical set T, there exists a proper almost symmetric numerical semigroup S with phi S equal to T. Both carriers include every possible finite nonempty gap set; no parameter cutoff or target additive closure is present.", DescribeRole.Definition),
            Entry("result", "The unrestricted event is false", resultFormula(),
                "Take T={0,1} union all naturals at least 4. Its complete gap set is {2,3}, with F=3. The complementary pairs {0,3} and {1,2} each have exactly one member, so T is proper and symmetric. It contains 1, whereas phi S omits 1 for every proper numerical semigroup S. Hence no proper almost symmetric semigroup has this image. The exclusion is analytic and quantifies over every possible source; there is no preimage enumeration or bound on source size. This gives an obstruction and a counterexample, without characterizing the full image.", DescribeRole.Theorem, false,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("delgado-suer-yesil-2026-symmetrization-surjectivity"),
                    ResolutionKind.Refuted))
        ), []));

    private static Formula membersFormula() =>
        All("U", NS(), All("n", N(), Equivalence(Member(F.Id("n"), At(Local("members"), F.Id("U"))), new Formula.Not(Member(F.Id("n"), Gaps(F.Id("U")))))));
    private static Formula frobeniusFormula() =>
        All("U", NS(), Equal(At(Local("frobenius"), F.Id("U")), At(Max, Gaps(F.Id("U")))));
    private static Formula SemigroupFormula() =>
        All("U", NS(), Equivalence(At(Local("Semigroup"), F.Id("U")), All("a", N(), All("b", N(), Imp(Member(F.Id("a"), At(Local("members"), F.Id("U"))), Imp(Member(F.Id("b"), At(Local("members"), F.Id("U"))), Member(Add(F.Id("a"), F.Id("b")), At(Local("members"), F.Id("U")))))))));
    private static Formula PseudoFrobeniusFormula() =>
        All("U", NS(), All("f", N(), Equivalence(At(Local("PseudoFrobenius"), F.Id("U"), F.Id("f")), And(Member(F.Id("f"), Gaps(F.Id("U"))), All("s", N(), Imp(Rel(F.Id("s"), FormulaRelationOperator.GreaterThan, D(0)), Imp(Member(F.Id("s"), At(Local("members"), F.Id("U"))), Member(Add(F.Id("f"), F.Id("s")), At(Local("members"), F.Id("U"))))))))));
    private static Formula AlmostSymmetricFormula() =>
        All("U", NS(), Equivalence(At(Local("AlmostSymmetric"), F.Id("U")), And(At(Local("Semigroup"), F.Id("U")), Equal(Multiply(D(2), Card(Gaps(F.Id("U")))), Add(At(Local("frobenius"), F.Id("U")), Card(Filter(Gaps(F.Id("U")), "f", At(Local("PseudoFrobenius"), F.Id("U"), F.Id("f")))))))));
    private static Formula SymmetricFormula() =>
        All("U", NS(), Equivalence(At(Local("Symmetric"), F.Id("U")), All("a", N(), Imp(Rel(F.Id("a"), FormulaRelationOperator.LessThanOrEqual, At(Local("frobenius"), F.Id("U"))), Equivalence(Member(F.Id("a"), At(Local("members"), F.Id("U"))), new Formula.Not(Member(Subtract(At(Local("frobenius"), F.Id("U")), F.Id("a")), At(Local("members"), F.Id("U")))))))));
    private static Formula rowLengthFormula() =>
        All("U", NS(), All("r", N(), Equal(At(Local("rowLength"), F.Id("U"), F.Id("r")), Card(Filter(At(Q("Finset", "range"), F.Id("r")), "a", Member(F.Id("a"), At(Local("members"), F.Id("U"))))))));
    private static Formula retainedRowsFormula() =>
        All("U", NS(), Equal(At(Local("retainedRows"), F.Id("U")), Filter(Gaps(F.Id("U")), "r", Or(Equal(F.Id("r"), At(Local("frobenius"), F.Id("U"))), new Formula.Not(At(Local("PseudoFrobenius"), F.Id("U"), F.Id("r")))))));
    private static Formula inverseBoundaryFormula() =>
        All("R", FinsetN(), All("l", Arrow(N(), N()), Equal(At(Local("inverseBoundary"), F.Id("R"), F.Id("l")), Image(F.Id("R"), "r", Add(At(F.Id("l"), F.Id("r")), Card(Filter(F.Id("R"), "q", Rel(F.Id("q"), FormulaRelationOperator.LessThan, F.Id("r")))))))));
    private static Formula deleteRowsFormula() =>
        All("U", NS(), All("R", FinsetN(), Equal(At(Local("deleteRows"), F.Id("U"), F.Id("R")), Image(F.Id("R"), "r", Subtract(F.Id("r"), Card(Filter(Seq(Gaps(F.Id("U")), Sp, Setminus, Sp, F.Id("R")), "q", Rel(F.Id("q"), FormulaRelationOperator.LessThan, F.Id("r")))))))));
    private static Formula phiFormula() =>
        All("U", NS(), All("n", N(), Equivalence(Member(F.Id("n"), At(Local("phi"), F.Id("U"))), new Formula.Not(Member(F.Id("n"), At(Local("deleteRows"), F.Id("U"), At(Local("retainedRows"), F.Id("U"))))))));
    private static Formula phiomitsoneFormula() =>
        All("U", NS(), Imp(At(Local("Semigroup"), F.Id("U")), new Formula.Not(Member(D(1), At(Local("phi"), F.Id("U"))))));
    private static Formula claimFormula() =>
        Equal(Typed(Local("claim"), Q("Prop")), All("T", NS(), Imp(At(Local("Symmetric"), F.Id("T")), Ex("S", NS(), And(At(Local("AlmostSymmetric"), F.Id("S")), Equal(At(Local("phi"), F.Id("S")), At(Local("members"), F.Id("T"))))))));
    private static Formula resultFormula() =>
        new Formula.Not(Local("claim"));

    private static DocumentBlock Entry(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature = true, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("delgado-phi-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Local(string name) => Q("D5", "S3", "Combinatorics", "Partitions", "DelgadoSuerYesilPhiRefutation", name);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts) { if (items.Count > 0) items.Add(Dot); items.Add(F.Id(part)); }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula NS() => Local("NumericalSet");
    private static Formula FinsetN() => At(Q("Finset"), N());
    private static Formula Gaps(Formula u) => At(Q("D5", "S3", "Combinatorics", "Partitions", "DelgadoSuerYesilPhiRefutation", "NumericalSet", "gaps"), u);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Member(Formula left, Formula right) => Rel(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Card(Formula set) => At(Q("Finset", "card"), set);
    private static Formula Typed(Formula value, Formula type) => Seq(Open, value, Colon, Sp, type, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(F.Id(name), type), Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula body) => Seq(LambdaLower, Sp, Typed(F.Id(name), N()), Sp, Mapsto, Sp, body);
    private static Formula Filter(Formula set, string name, Formula body) => At(Q("Finset", "filter"), LambdaOf(name, body), set);
    private static Formula Image(Formula set, string name, Formula body) => At(Q("Finset", "image"), LambdaOf(name, body), set);
}
