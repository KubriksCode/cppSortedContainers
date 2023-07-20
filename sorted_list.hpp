#pragma once

#include <cstddef> // useful typedefs
#include <cstdint> // useful typedefs
#include <vector> // basic container of the class
#include <algorithm> // lower_bound, upper_bound
#include <exception> // custom exception class
#include <iterator> // move iterators
#include <ranges> // requires c++20, used for lazy iterator implementation

namespace srv = std::ranges::views;

// does not implement methods for const sorted_list (for now at least)
// does not implement slicing (Python) or negative indexes

// namespace sorted_containters
namespace sortc{

template<class T, class allocator = std::allocator<T>>
class sorted_list{ 
	// typedefs
	private:
		using vec_t = std::vector<T, allocator>;
		using container_t = std::vector<vec_t>;
		using len_t = typename vec_t::size_type; /* size_t usually */
		using tree_t = std::vector<len_t>; 
		using pair_t = std::pair<len_t, len_t>;
	public:
		using this_t = sorted_list<T>;
		using value_t = T;
		using index_t = len_t; /* index_t is type for indexing */
		static constexpr len_t LOAD_FACTOR = 100;
		
	// class implementation
	private:
		len_t _len;
		len_t _load;
		container_t _list;
		vec_t _max;
		tree_t _index;
		len_t _off;

		class err : std::exception{
			private:
				std::string msg;
			
			public:
				err(const char* str) : msg(str){
				}

				const char* what() const noexcept override{
					return msg.c_str();
				}
		};

		// returns the "bitmask" of the number
		static len_t _bit_trick(len_t sz){
			--sz; // evil workaround to perfect powers of 2

			sz |= sz >> 1;
			sz |= sz >> 2;
			sz |= sz >> 4;
			sz |= sz >> 8;
			sz |= sz >> 16;
			
			// static check
			if constexpr(sizeof(len_t) == 8) 
				sz |= sz >> 32;
			
			return sz;

			/*
				TODO possible better implementation

				--sz; // evil wokaround to perfect powers of 2

				len_t mask = 1;
				for (len_t i = 2; i < sizeof(len_t); ++i, mask <<= 1)
					sz |= sz >> mask;

				return sz;
			*/
		}

		// build index
		void _build_index(){
			if (_list.size() == 1){
				_index.push_back(_list[0].size());
				_off = 0;
				return;
			}

			len_t index_sz = _bit_trick(_list.size());
			len_t aux_sz = index_sz >> 1; // index first row
			
			_index.resize(index_sz + _list.size());
			
			index_t i;
			for (i = index_sz; i < _index.size(); ++i) 
				_index[i] = _list[i - index_sz].size();
				
			const index_t end = aux_sz + (_list.size() >> 1);
			for (i = aux_sz; i < end; ++i){
				_index[i] = _index[(i << 1) + 1] + _index[(i << 1) + 2];
			}
				
			if (_list.size() & 1) _index[i] = _list.back().size();
			
			// evil workaround for unsigned numbers
			for (i = aux_sz; i-- > 0;) 
				_index[i] = _index[(i << 1) + 1] + _index[(i << 1) + 2];
			
			_off = index_sz;
		}

		void _expand(index_t i){
			// case expand (the list has a size > than _load << 1)
			if (_list[i].size() > _load << 1){
				// emplace + move should be more efficient
				_max.insert(_max.begin() + i + 1, _list[i].back());
				_list.emplace(_list.begin() + i + 1, 
							std::move_iterator(_list[i].begin() + _load),
							std::move_iterator(_list[i].end()));

				_list[i].resize(_load);
				_max[i] = _list[i].back();

				_index.clear();
				return;
			}

			// index is a vectorized tree-like structure 
			if (_index.size()){
				index_t child = _off + i;
				while (child){ 
					++_index[child];
					child = (child - 1) >> 1;
				}
				++_index[0];
			}
		}

		// removes element
		void _delete(index_t i, index_t j){
			_list[i].erase(_list[i].begin() + j);
			--_len;

			len_t llen = _list[i].size();

			if (llen > (_load >> 1)){
				_max[i] = _list[i].back();

				if (_index.size()){
					index_t child = _off + i;
					while (child){
						--_index[child];
						child = (child - 1) >> 1;
					}
					--_index[0];
				}

				return;
			}
			if (_list.size() > 1){
				/*
				if (!i) 
					++i;
				*/
				i += !i; // increment i only if it's 0

				index_t prev = i - 1;
				_list[prev].reserve(_list[prev].size() + _list[i].size());
				// move semantics
				std::move(_list[i].begin(), _list[i].end(), 
					std::back_inserter(_list[prev]));
				_max[prev] = _list[prev].back();

				_list.erase(_list.begin() + i);
				_max.erase(_max.begin() + i);
				_index.clear();

				this->_expand(prev);

				return;
			}
			if (!llen){
				_list.erase(_list.begin() + i);
				_max.erase(_max.begin() + i);
				_index.clear();
				return;
			}
			_max[i] = _list[i].back();
		}

		// from index pair (v[i][j]) to single index (v[x])
		index_t _locate(index_t i, index_t j){
			if (!i)
				return j;
			
			if (!_index.size())
				this->_build_index();

			len_t total = 0;
			i += _off;

			while (i){
				if (!(i & 1))
					total += _index[i - 1];

				i = (i - 1) >> 1;
			}

			return total + j;
		}

		// inverse of _locate
		// index_t is an unsigned value
		pair_t _place(index_t i){
			if (i > _len)
				throw err("Index out of range");
			
			if (i < _list[0].size())
				return pair_t(0, i);

			if (!_index.size())
				this->_build_index();

			index_t pos = 0;
			index_t child = 1;
			len_t idx_len = _index.size();

			while (child < idx_len){
				index_t idx_child = _index[child];

				if (i < idx_child)
					pos = child;
				else{
					i -= idx_child;
					pos = child + 1;
				}

				child = (pos << 1) + 1;
			}

			return pair_t(pos - _off, i);
		}

	public:
		// we assume operator <=>
		sorted_list() noexcept : _len(0UL), _load(LOAD_FACTOR),
			_list(container_t()), _max(vec_t()), _index(tree_t()), _off(0U){
		}

		// TODO, not implemented due to the lack of update method
		// explicit sorted_list(it begin, it end)
		
		sorted_list(const sorted_list&) = default;
		sorted_list(sorted_list&&) noexcept = default;
		sorted_list& operator=(const sorted_list&) = default;
		sorted_list& operator=(sorted_list&&) noexcept = default;
		
		virtual ~sorted_list(){
		}

		// TODO, not implemented because it requires a sorted iterable
		// update(it begin, it end) 

		void clear(){
			_len = 0;
			_list.clear();
			_max.clear();
			_index.clear();
			_off = 0;
		}

		void add(const value_t& el){
			// case empty container
			if (!_max.size()){
				_list.emplace_back();
				_list[0].push_back(el);
				_max.push_back(el);
				++_len;

				return;
			}

			// call "bisect_right"
			auto it = std::upper_bound(_max.begin(), _max.end(), el); 
			index_t i = it - _max.begin(); // index

			if (i == _max.size()){
				_list[--i].push_back(el);
				_max[i]= el;
			}
			else{
				it = std::upper_bound(_list[i].begin(), _list[i].end(), el);
				_list[i].insert(it, el);
			}
			
			this->_expand(i);
			++_len;
		}

		// move semantics
		void add(value_t&& el){
			// case empty container
			if (!_max.size()){
				_list.emplace_back();
				_list[0].push_back(el);
				_max.push_back(std::move(el));
				++_len;

				return;
			}

			// call "bisect_right"
			auto it = std::upper_bound(_max.begin(), _max.end(), el); 
			index_t i = it - _max.begin(); // index

			if (i == _max.size()){
				_list[--i].push_back(el);
				_max[i]= std::move(el);
			}
			else{
				it = std::upper_bound(_list[i].begin(), _list[i].end(), el);
				_list[i].insert(it, std::move(el));
			}
			
			this->_expand(i);
			++_len;
		}

		// NB emplace it's not implemented, feels uselss

		// membership test
		bool contains(const value_t& el){
			if (!_max.size())
				return false;

			auto it = std::lower_bound(_max.begin(), _max.end(), el);
			index_t i = it - _max.begin();

			if (i == _max.size())
				return false;

			it = std::lower_bound(_list[i].begin(), _list[i].end(), el);
			return *it == el;
		}

		// returns the first index of the value
		// reaises exception if the value is not found
		index_t find(const value_t& el){
			if (!_len)
				throw err("Element not found");

			auto it = std::lower_bound(_max.begin(), _max.end(), el);
			index_t i = it - _max.begin();

			if (i == _max.size())
				throw err("Element not found");
				
			it = std::lower_bound(_list[i].begin(), _list[i].end(), el);
			index_t j = it - _list[i].begin();

			if (_list[i][j] != el)
				throw err("Element not found");
			
			return _locate(i, j);
		}

		// number of occurrences 
		len_t count(const value_t& el){
			if (!_max.size())
				return 0;

			auto it = std::lower_bound(_max.begin(), _max.end(), el);
			index_t i = it - _max.begin();

			if (i == _max.size())
				return 0;

			it = std::lower_bound(_list[i].begin(), _list[i].end(), el);
			index_t left = it - _list[i].begin();
			it = std::upper_bound(_max.begin(), _max.end(), el);
			index_t j = it - _max.begin();

			if (j == _max.size())
				return _len - _locate(i, left);

			it = std::upper_bound(_list[j].begin(), _list[j].end(), el);
			index_t right = it - _list[j].begin();

			if (i == j)
				return right - left;

			return _locate(j, right) - _locate(i, left);
		}

		// removes last (biggest) element of the list, enables usage
		// as a priority queue (prob suboptimal)
		value_t pop(){
			if (!_len)
				throw err("List is empty");

			index_t i = _list.size() - 1;
			index_t j = _list[i].size() - 1;
			value_t tmp = _list[i][j];
			_delete(i, j);
			return tmp;
		}

		// removes value in the list (only one occurence)
		bool remove(const value_t& el){
			if (!_max.size())
				return false;

			auto it = std::lower_bound(_max.begin(), _max.end(), el);
			index_t i = it - _max.begin();

			if (i == _max.size())
				return false;

			it = std::lower_bound(_list[i].begin(), _list[i].end(), el);
			index_t j = it - _list[i].begin();

			if (_list[i][j] != el)
				return false;

			_delete(i, j);			
			return true;
		}

		// removes value at given index
		// returns the deleted element, raises exception if index out of bound
		value_t remove_at(index_t i){
			if (!_len)
				throw err("Index out of range");

			/*
			if (!i){
				auto tmp = _list[0][0];
				_delete(0, 0);
				return tmp;
			}
			*/
			if (i < _list[0].size()){
				auto tmp = _list[0][i];
				_delete(0, i);
				return tmp;
			}

			auto [j, k] = _place(i);
			auto tmp = _list[j][k];
			_delete(j, k);
			return tmp;
		}

		// return const reference to obj at index i
		const value_t& operator[](index_t i){
			auto [j, k] = _place(i);
			return _list[j][k];
		}
		
		// iterators alternative (lazy, TODO real iterators)
		// NB views get invalidted, just like iterators
		auto get_view(){
			const container_t& _hack = _list;
			return _hack | srv::join;
		}

		[[nodiscard]] inline len_t size(){
			return _len;
		}
};

}
