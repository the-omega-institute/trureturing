using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635StateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A previous row and remaining defect budget determine the transfer state.", H("Boundary states"),
        Blocks(
            Describe.Lean(DescribeId.Create("state"),
                DeclarationHandle.Create(Prefix + "State"), H("Transfer indices"),
                StatementSource.FromAuthor(Disp(Equal(Call("State"), Call("Fin", D(1, 2, 7))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The index type has 127 elements."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fresh-index-type"),
                DeclarationHandle.Create(Prefix + "Fresh"), H("Fresh-state indices"),
                StatementSource.FromAuthor(Disp(Equal(Call("Fresh"), Call("Fin", D(9, 6))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The index type has 96 elements."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row-number"),
                DeclarationHandle.Create(Prefix + "RowNumber"), H("Labelled row indices"),
                StatementSource.FromAuthor(Disp(Equal(Call("RowNumber"), Call("Fin", D(7, 2, 9))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The index type has 729 elements."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("h"),
                DeclarationHandle.Create(Prefix + "h"), H("Horizontal defects in a row"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), Equal(Call("h", V("p")), Call("bondDefects", Call("horizontal"), V("p"), V("p")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The count includes each monochromatic horizontal bond once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cost"),
                DeclarationHandle.Create(Prefix + "cost"), H("Defect cost of adding a row"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("r", Call("Row"), Equal(Call("cost", V("p"), V("r")), Add(Call("bondDefects", Call("between"), V("p"), V("r")), Call("h", V("r")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Adding a row pays for both adjacent-row diagonals and all horizontal defects of the new row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Validity of a row and budget"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), IffFormula(Call("Valid", V("p"), V("d")), AtMost(Add(Call("h", V("p")), V("d")), D(2))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A boundary row and its remaining defect budget must fit within the total allowance of two."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inst-decidable-valid"),
                DeclarationHandle.Create(Prefix + "instDecidableValid"), H("Decidability of a boundary state"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), Equal(Call("instDecidableValid", V("p"), V("d")), Call("inferInstanceAs", Call("Decidable", AtMost(Add(Call("h", V("p")), V("d")), D(2))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The validity test is the natural-number comparison of the horizontal defects plus the remaining budget with two."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row-equiv"),
                DeclarationHandle.Create(Prefix + "rowEquiv"), H("Numbering of labelled rows"),
                StatementSource.FromAuthor(Disp(Equal(Call("rowEquiv"), Call("Equiv.symm", Call("finFunctionFinEquiv", D(3), D(6)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The inverse of the base-three finite-function equivalence enumerates the six entries of every labelled row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rep"),
                DeclarationHandle.Create(Prefix + "rep"), H("Representative of a fresh state"),
                StatementSource.FromAuthor(Disp(All("i", Call("Fresh"), Equal(Call("rep", V("i")), Call("rowEquiv", Call("Fin.ofNat", D(7, 2, 9), Call("Option.getD", Call("Array.getElemOptional", Call("representativeNumbers"), Call("Fin.val", V("i"))), D(0)))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The table gives row numbers for the 96 canonical equality patterns with at most two horizontal defects."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("budget"),
                DeclarationHandle.Create(Prefix + "budget"), H("Remaining budget of a fresh state"),
                StatementSource.FromAuthor(Disp(All("i", Call("Fresh"), Equal(Call("budget", V("i")), Sub(D(2), Call("h", Call("rep", V("i")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The remaining budget is the total allowance less the representative row's horizontal defects."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fresh"),
                DeclarationHandle.Create(Prefix + "fresh"), H("Index of the equality pattern"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), Equal(Call("fresh", V("p")), Call("Fin.ofNat", D(9, 6), Call("List.idxOf", Call("rowCode", V("p")), Call("representativeCodes"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The row code records equality for each pair of columns. The search locates that code in the fresh pattern table."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Transfer class of a boundary state"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), Equal(Call("cl", V("p"), V("d")), IfThenElse(AtMost(Add(Call("h", V("p")), V("d")), D(1)), Call("Fin.castAdd", D(9, 6), Call("HardinA229532StripData.cl", V("p"), V("d"))), Call("Fin.natAdd", D(3, 1), Call("fresh", V("p"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The 31 inherited states cover rows and budgets with sum at most one. All other valid states use the fresh pattern index after that block."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("destination"),
                DeclarationHandle.Create(Prefix + "destination"), H("Destination of a candidate successor"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), All("r", Call("Row"), Equal(Call("destination", V("p"), V("d"), V("r")), IfThenElse(AtMost(Call("cost", V("p"), V("r")), V("d")), Call("some", Call("cl", V("r"), Sub(V("d"), Call("cost", V("p"), V("r"))))), Call("none")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The available budget guards the subtraction. A legal transition records the successor row with its updated budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("outgoing"),
                DeclarationHandle.Create(Prefix + "outgoing"), H("Full weighted successor list"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), Equal(Call("outgoing", V("p"), V("d")), Call("List.filterMap", Call("destination", V("p"), V("d")), Call("List.ofFn", Call("rowEquiv")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The list examines every labelled row and retains one class entry for each affordable move."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("start-class"),
                DeclarationHandle.Create(Prefix + "startClass"), H("Class for a candidate first row"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), Equal(Call("startClass", V("p")), IfThenElse(AtMost(Call("h", V("p")), D(2)), Call("some", Call("cl", V("p"), Sub(D(2), Call("h", V("p"))))), Call("none")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first row uses only its horizontal defects and starts from allowance two."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("start-classes"),
                DeclarationHandle.Create(Prefix + "startClasses"), H("List of allowed first-row classes"),
                StatementSource.FromAuthor(Disp(Equal(Call("startClasses"), Call("List.filterMap", Call("startClass"), Call("List.ofFn", Call("rowEquiv")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Enumerating all labelled rows gives the initial class multiplicities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count-classes"),
                DeclarationHandle.Create(Prefix + "count_classes"), H("Filter-map multiplicities"),
                StatementSource.FromAuthor(Disp(All("f", Arrow(Call("Row"), Call("Option", Call("State"))), All("s", Call("State"), Equal(AsInt(Call("List.count", V("s"), Call("List.filterMap", V("f"), Call("List.ofFn", Call("rowEquiv"))))), SumOver("r", Call("Row"), IfThenElse(Equal(App(V("f"), V("r")), Call("some", V("s"))), D(1), D(0)))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Filtering a complete list of rows and counting an output class agrees with summing its indicator over all rows."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("outgoing-count"),
                DeclarationHandle.Create(Prefix + "outgoing_count"), H("Entry of the weighted successor vector"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), All("s", Call("State"), Equal(AsInt(Call("List.count", V("s"), Call("outgoing", V("p"), V("d")))), SumOver("r", Call("Row"), IfThenElse(And(AtMost(Call("cost", V("p"), V("r")), V("d")), Equal(Call("cl", V("r"), Sub(V("d"), Call("cost", V("p"), V("r")))), V("s"))), D(1), D(0))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The indicator imposes both affordability and the destination class after payment."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("start-count"),
                DeclarationHandle.Create(Prefix + "start_count"), H("Entry of the first-row vector"),
                StatementSource.FromAuthor(Disp(All("s", Call("State"), Equal(AsInt(Call("List.count", V("s"), Call("startClasses"))), SumOver("r", Call("Row"), IfThenElse(And(AtMost(Call("h", V("r")), D(2)), Equal(Call("cl", V("r"), Sub(D(2), Call("h", V("r")))), V("s"))), D(1), D(0))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The indicator enforces the two-defect allowance and the class of the resulting first row."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("h-relabel"),
                DeclarationHandle.Create(Prefix + "h_relabel"), H("Horizontal cost is relabelling invariant"),
                StatementSource.FromAuthor(Disp(All("e", Call("Equiv.Perm", Call("Fin", D(3))), All("p", Call("Row"), Equal(Call("h", Compose(V("e"), V("p"))), Call("h", V("p"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A common colour permutation preserves endpoint equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cost-relabel"),
                DeclarationHandle.Create(Prefix + "cost_relabel"), H("Transition cost is relabelling invariant"),
                StatementSource.FromAuthor(Disp(All("e", Call("Equiv.Perm", Call("Fin", D(3))), All("p", Call("Row"), All("r", Call("Row"), Equal(Call("cost", Compose(V("e"), V("p")), Compose(V("e"), V("r"))), Call("cost", V("p"), V("r")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The same permutation acts on both rows and preserves all three types of bond defects."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cl-relabel"),
                DeclarationHandle.Create(Prefix + "cl_relabel"), H("Class is relabelling invariant"),
                StatementSource.FromAuthor(Disp(All("e", Call("Equiv.Perm", Call("Fin", D(3))), All("p", Call("Row"), All("d", Call("Nat"), Equal(Call("cl", Compose(V("e"), V("p")), V("d")), Call("cl", V("p"), V("d")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Both the inherited and fresh class maps depend on equality patterns and the remaining budget."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("legal"),
                DeclarationHandle.Create(Prefix + "legal"), H("Closure of valid states"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), All("r", Call("Row"), ImpliesFormula(Call("Valid", V("p"), V("d")), ImpliesFormula(AtMost(Call("cost", V("p"), V("r")), V("d")), Call("Valid", V("r"), Sub(V("d"), Call("cost", V("p"), V("r"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("After an affordable move the new horizontal cost plus the new budget is at most the old budget."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closed"),
                DeclarationHandle.Create(Prefix + "closed"), H("Closure of the inherited block"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("r", Call("Row"), All("d", Call("Nat"), ImpliesFormula(AtMost(Add(Call("h", V("p")), V("d")), D(1)), ImpliesFormula(AtMost(Call("cost", V("p"), V("r")), V("d")), AtMost(Add(Call("h", V("r")), Sub(V("d"), Call("cost", V("p"), V("r")))), D(1))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A transition from the one-defect sector stays in the inherited block."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("legal-start"),
                DeclarationHandle.Create(Prefix + "legal_start"), H("Validity of an allowed first row"),
                StatementSource.FromAuthor(Disp(All("r", Call("Row"), ImpliesFormula(AtMost(Call("h", V("r")), D(2)), Call("Valid", V("r"), Sub(D(2), Call("h", V("r")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("First-row payment leaves budget two minus the horizontal cost."))), DescribeRole.Theorem))));

    private static Formula V(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Word(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] arguments)
        {
            Formula symbol = Seq(name.Split('.').SelectMany((part, index) =>
                index == 0 ? new[] { Word(part) } : new[] { Dot, Word(part) }).ToArray());
            return arguments.Length == 0 ? symbol : App(symbol, arguments);
        }
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula AtMost(Formula left, Formula right) => Seq(left, Sp, Le, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) => Seq(Paren(left), Sp, Land, Sp, Paren(right));
    private static Formula ImpliesFormula(Formula left, Formula right) => Seq(Paren(left), Sp, Implies, Sp, Paren(right));
    private static Formula IffFormula(Formula left, Formula right) => Seq(Paren(left), Sp, Iff, Sp, Paren(right));
    private static Formula Arrow(Formula left, Formula right) => Seq(Paren(left), Sp, To, Sp, Paren(right));
    private static Formula Compose(Formula left, Formula right) => Seq(Paren(left), Sp, Circ, Sp, Paren(right));
    private static Formula AsInt(Formula value) => Paren(Seq(value, Colon, Sp, Int));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
    private static Formula IfThenElse(Formula guard, Formula yes, Formula no) =>
            Paren(Seq(Word("if"), Sp, guard, Sp, Word("then"), Sp, yes, Sp, Word("else"), Sp, no));
    private static Formula SumOver(string name, Formula type, Formula body) =>
            Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Paren(body));
}
