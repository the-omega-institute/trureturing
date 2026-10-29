using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class SeedQueueInvariantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appending a dyadic list and retaining its affordable prefix preserves ancestor heights and bounds the peak at a first omission.",
        H("Deferred-prefix ancestor invariant"),
        Blocks(
            Describe.Lean(DescribeId.Create("deferred-prefix-ancestor-invariant"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/SeedQueueInvariant.deferred_prefix_invariant"),
                H("Physical splitting, exact landing and the ancestor range"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Weights f are integers on arbitrary physical labels. A queue has ancestor range [0,D] relative to mu if, for each occurrence q, its value minus mu minus the mass preceding that occurrence lies in [0,D]. Equal values do not identify occurrences. Append a dyadic list with seed a. If that list is nonempty, assume its birth height a-mu-mass(old) lies in [0,D]. Each appended dyadic occurrence has exactly that birth height; retaining an initial segment preserves the preceding mass of each retained occurrence.")),
                    Paragraph(Text("The recursive splitBudget consumes labels from the front while the next weight fits the remaining budget. It returns a literal prefix q and literal suffix e of old++small, with mass(q)<=b-mu. For positive weights this is the longest affordable initial segment. With native transport mass(small)-(B-p)=b-a and 2(C-B)=b-1, the postnegative height is h=b-mu-mass(q)>=0, and direct mass conservation gives oldHeight+mass(e)+p-B=h. If x is the first emitted label, maximality gives b-mu<mass(q)+f(x). Its remembered ancestor height delta=f(x)-mu-mass(q) lies in [0,D], implying h<f(x) and B+h<=C+floor(D/2). If e is empty, the peak is exactly oldHeight+p. If b=mu and every input weight is positive, the retained queue is empty and the landing height is zero, so every currently available occurrence is emitted.")),
                    Paragraph(Text("The arithmetic and ancestor step itself does not require positive weights; positivity is needed to interpret the split as the longest affordable prefix, to force an empty queue at final zero budget, and to control intermediate positive heights. This local theorem has no supplied completion word or recovery witness. It does not by itself derive native seed extrema, partition the native source, iterate the queue through all chains, or recover the complete inventory. NativeSeedChains supplies individual native transport chains. A full source-coupled adaptive-width theorem and the original exact-C objective remain open."))),
                DescribeRole.Theorem)), []));
}
