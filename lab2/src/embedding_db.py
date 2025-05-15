import os
import numpy as np
import requests
from bs4 import BeautifulSoup
from openai import OpenAI
import tiktoken  # For token counting
import PyPDF2
from src.embedding_models import BaseEmbeddingModel, OpenAIEmbeddingModel, MiniEmbeddingModel
import pickle 

client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

class VectorDB:
    def __init__(self, directory="documents", vector_file="embeddings.npy", max_words_per_chunk=4000, embedding_model: BaseEmbeddingModel = OpenAIEmbeddingModel()):
        """
        Initializes the in-memory database by processing text files and generating embeddings.
        """
        self.directory = directory
        self.vector_file = vector_file
        self.chunks_file = os.path.splitext(vector_file)[0] + "_chunks.pkl"
        self.max_words_per_chunk = max_words_per_chunk
        self.embedding_model = embedding_model
        
        docs = self.read_text_files()
        print(f"[VectorDB] Reading all of the documents in {self.directory}.")
        
        self.chunks = self.embedding_model.split_documents(docs)
        print(f"[VectorDB] Splitting the knowledge base into {len(self.chunks)} chunks. Saving the chunks")
        with open(self.chunks_file, 'wb') as f:
            pickle.dump(self.chunks, f)
            print(f"[VectorDB] Chunks saved to {self.chunks_file}")
        
        # Get embeddings from the model
        embeddings_data = self.embedding_model.get_embeddings_batch(self.chunks)
        self.embeddings = embeddings_data
        print(f"[VectorDB] Generated {len(self.embeddings)} embeddings with shape {self.embeddings.shape}. Stored at {self.vector_file}")
        
        self.store_embeddings()

    
    @staticmethod
    def scrape_website(url: str, output_file: str):
        """
        Fetches the main content of a given URL and saves it to an output file.
        Handles both HTML pages and PDF files.
        """
        try:
            response = requests.get(url)
            response.raise_for_status()
            content_type = response.headers.get('Content-Type', '')

            if 'application/pdf' in content_type or url.endswith('.pdf'):
                with open(output_file, 'wb') as file:
                    file.write(response.content)
                try:
                    with open(output_file, 'rb') as pdf_file:
                        reader = PyPDF2.PdfReader(pdf_file)
                        text = "\n".join([page.extract_text() for page in reader.pages])
                    text_output_file = os.path.splitext(output_file)[0] + '.txt'
                    with open(text_output_file, 'w', encoding='utf-8') as text_file:
                        text_file.write(text)
                    print(f"PDF content extracted and saved to {text_output_file}")
                except Exception as e:
                    print(f"Error extracting text from PDF: {e}")

            elif 'text/html' in content_type:
                soup = BeautifulSoup(response.text, "html.parser")
                text_content = soup.get_text(separator="\n", strip=True)
                with open(output_file, 'w', encoding='utf-8') as file:
                    file.write(text_content)
                print(f"HTML content saved to {output_file}")
            else:
                print(f"Unsupported content type: {content_type}")
        
        except requests.exceptions.RequestException as e:
            print(f"Error fetching the URL: {e}")

    def read_text_files(self):
        """
        Reads all text files in the directory and returns their content as a list.
        """
        documents = []
        for filename in os.listdir(self.directory):
            if filename.endswith(".txt"):
                print(f"[VectorDB.read_text_files] Reading {filename}.")
                with open(os.path.join(self.directory, filename), 'r', encoding='utf-8') as file:
                    documents.append(file.read())
        return documents
    
    def store_embeddings(self):
        """
        Saves the numpy matrix of embeddings to a .npy file.
        """
        np.save(self.vector_file, self.embeddings)
        print(f"[VectorDB.store_embeddings] Embeddings saved to {self.vector_file}")
    
    @staticmethod
    def cosine_similarity(vector1, vector2):
        """
        Calculate cosine similarity between two vectors.
        Returns a value between -1 and 1, where 1 means identical vectors.
        """
        dot_product = np.dot(vector1, vector2)
        
        magnitude1 = np.sqrt(np.sum(np.square(vector1)))
        magnitude2 = np.sqrt(np.sum(np.square(vector2)))
        
        if magnitude1 == 0 or magnitude2 == 0:
            return 0
        
        return dot_product / (magnitude1 * magnitude2)

    @staticmethod
    def get_top_k(npy_file: str, embedding_model: BaseEmbeddingModel, query: str, k: int = 5, verbose: bool = False):
        """
        Returns top-k most similar chunks and their scores.
        """
        # Load embeddings from .npy file
        stored_embeddings = np.load(npy_file)
        
        # Load chunks from corresponding .pkl file
        chunks_file = os.path.splitext(npy_file)[0] + "_chunks.pkl"
        with open(chunks_file, 'rb') as f:
            chunks = pickle.load(f)
        
        # Generate embedding for the query
        query_embedding = embedding_model.get_embedding(query)
        
        # Calculate similarities
        similarities = [VectorDB.cosine_similarity(query_embedding, embedding) 
                        for embedding in stored_embeddings]
        
        # Get top k indices
        top_k_indices = np.argsort(similarities)[-k:][::-1]
        top_k_indices = top_k_indices.flatten()
        
        # Retrieve top-k chunks and their similarities
        top_k_chunks = [chunks[index] for index in top_k_indices]
        top_k_scores = [similarities[index] for index in top_k_indices]
        
        # Output the chunks and scores
        if verbose:
            for i, (chunk, score) in enumerate(zip(top_k_chunks, top_k_scores)):
                print(f"Result #{i+1} (Score: {score:.4f})")
                print(f"{chunk[:200]}...")
                print("-" * 50)

        return top_k_chunks, top_k_scores


if __name__ == "__main__":
    # Create and save the database
    openai_embedding_model = OpenAIEmbeddingModel()
    mini_embedding_model = MiniEmbeddingModel()

    # Name of the file that stores the embeddings in memory. 
    embedding_database_file = "database.npy"

    vector_db = VectorDB(directory="documents", 
                         vector_file=embedding_database_file, 
                         embedding_model=openai_embedding_model)

    # Example usage of querying the database. 
    query = "What is reinforcement learning?"
    top_k_results = VectorDB.get_top_k(embedding_database_file, openai_embedding_model, query, k=3, verbose=True)
