from abc import ABC, abstractmethod
from sentence_transformers import SentenceTransformer
import numpy as np
import tiktoken
import os
from openai import OpenAI
from abc import ABC, abstractmethod
import numpy as np
from typing import List, Tuple

class BaseEmbeddingModel(ABC):
    """Abstract base class for embedding models with chunking support"""
    def __init__(self):
        self.max_tokens = 512  # Default value
        self.tokenizer = None  # Must be initialized in subclasses
        
    @abstractmethod
    def get_embedding(self, text: str) -> List[float]:
        """Generate embedding for a single text input"""
        pass
    
    def split_documents(self, documents: List[str]) -> List[str]:
        """
        Split documents into model-appropriate chunks
        - First splits by <EOC> tags
        - Then splits remaining chunks by token limits
        """
        final_chunks = []
        
        for doc in documents:
            # First split by EOC markers
            parts = [p.strip() for p in doc.split('<EOC>') if p.strip()]
            
            for part in parts:
                # Tokenize using model-specific tokenizer
                tokens = self.tokenizer.encode(part)
                
                # Adding a warning for documents / parts that exceed token limit.
                if len(tokens) > self.max_tokens:
                    preview = part[:15]  # Preview first 15 characters of the part
                    print(f"[embedding_models.py] Warning: Document / part exceeds token limit of {self.max_tokens}. Length: {len(tokens)}. Preview: '{preview}'...")

                
                # Split into chunks respecting max_tokens
                for i in range(0, len(tokens), self.max_tokens):
                    if len(tokens) > self.max_tokens:
                        preview_chunk = self.tokenizer.decode(tokens[i:i + self.max_tokens])[:15]  # Preview first 15 characters of the chunk
                        print(f"[embedding_models.py] Warning: Chunk exceeds token limit of {self.max_tokens}. Saving {len(tokens[i:i+self.max_tokens])} tokens {i}-{i+len(tokens[i:i+self.max_tokens])} (out of {len(tokens)}). Preview: '{preview_chunk}'...")
                    
                    chunk_tokens = tokens[i:i+self.max_tokens]
                    final_chunks.append(
                        self.tokenizer.decode(chunk_tokens)
                    )
        
        return final_chunks
    
    def get_embeddings_batch(self, texts: List[str]) -> List[Tuple[np.ndarray, str]]:
        """Batch process embeddings with text pairing"""
        return np.array([self.get_embedding(text) for text in texts])

class MiniEmbeddingModel(BaseEmbeddingModel):
    def __init__(self, model_name="all-MiniLM-L6-v2"):
        super().__init__()
        from sentence_transformers import SentenceTransformer
        self.model = SentenceTransformer(model_name)
        self.tokenizer = self.model.tokenizer
        self.max_tokens = 256  # Model's actual max sequence length
        
    def get_embedding(self, text: str) -> Tuple[List[float], str]:
        """Return embedding with original text"""
        embedding = self.model.encode(
            text,
            convert_to_tensor=False,
            normalize_embeddings=True,
            show_progress_bar=False
        )
        return embedding.tolist()
    
    def get_embeddings_batch(self, texts: List[str]) -> List[Tuple[np.ndarray, str]]:
        """Optimized batch processing with text pairing"""
        embeddings = self.model.encode(
            texts,
            batch_size=32,
            convert_to_tensor=False,
            normalize_embeddings=True,
            show_progress_bar=False
        )
        return embeddings

class OpenAIEmbeddingModel(BaseEmbeddingModel):
    def __init__(self, model_name="text-embedding-3-small"):
        super().__init__()
        import tiktoken
        self.client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        self.model_name = model_name
        self.tokenizer = tiktoken.get_encoding("cl100k_base")
        self.max_tokens = 8191  # OpenAI's limit
        
    def get_embedding(self, text: str) -> Tuple[List[float], str]:
        """Return OpenAI embedding with original text"""
        # Truncation logic remains the same
        response = self.client.embeddings.create(
            input=text,
            model=self.model_name
        )
        return response.data[0].embedding