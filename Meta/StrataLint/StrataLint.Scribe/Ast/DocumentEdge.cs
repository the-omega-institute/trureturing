namespace StrataLint.Scribe;

public abstract class NarrativeTarget
{
    private protected NarrativeTarget() { }

    public sealed class Document : NarrativeTarget
    {
        internal Document(GidRef documentGid) =>
            DocumentGid = documentGid ?? throw new ArgumentNullException(nameof(documentGid));

        public GidRef DocumentGid { get; }
    }

    public sealed class Describe : NarrativeTarget
    {
        internal Describe(GidRef documentGid, DescribeId describeId)
        {
            DocumentGid = documentGid ?? throw new ArgumentNullException(nameof(documentGid));
            DescribeId = describeId ?? throw new ArgumentNullException(nameof(describeId));
        }

        public GidRef DocumentGid { get; }

        public DescribeId DescribeId { get; }
    }
}

public abstract class DocumentEdge
{
    private protected DocumentEdge() { }

    public sealed class TruthAnchor : DocumentEdge
    {
        private TruthAnchor(LeanDeclarationRef target) => Target = target;

        public LeanDeclarationRef Target { get; }

        public static TruthAnchor Create(LeanDeclarationRef target)
        {
            ArgumentNullException.ThrowIfNull(target);
            return new TruthAnchor(target);
        }
    }

    public sealed class Dependency : DocumentEdge
    {
        private Dependency(GidRef target) => Target = target;

        public GidRef Target { get; }

        public static Dependency Create(GidRef target)
        {
            RequireDocumentGid(target);
            return new Dependency(target);
        }
    }

    public sealed class NarrativeReference : DocumentEdge
    {
        private NarrativeReference(NarrativeTarget target) => Target = target;

        public NarrativeTarget Target { get; }

        public static NarrativeReference ToDocument(GidRef target)
        {
            RequireDocumentGid(target);
            return new NarrativeReference(new NarrativeTarget.Document(target));
        }

        public static NarrativeReference ToDescribe(GidRef document, DescribeId describe)
        {
            RequireDocumentGid(document);
            ArgumentNullException.ThrowIfNull(describe);
            return new NarrativeReference(new NarrativeTarget.Describe(document, describe));
        }
    }

    private static void RequireDocumentGid(GidRef target)
    {
        ArgumentNullException.ThrowIfNull(target);
        if (!target.IsFormalModule)
        {
            throw new ArgumentException(
                "Document edge target must identify a Scribe document GID.",
                nameof(target));
        }
    }
}
